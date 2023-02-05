open Core

type t = {graph: Graph.t; pos: int; port: int; conn: int list}
[@@deriving yojson, fields]

let empty ~max_conn = {graph= Graph.empty ~max_conn; pos= 0; port= 0; conn= []}

let selected s = Option.map ~f:snd @@ Map.find s.graph.edges (s.pos, s.port)

let of_graph g = {graph= g; pos= 0; port= 0; conn= []}

let has_isolated s = Graph.n_components @@ graph s > 1

let has_conn s = not (List.is_empty @@ conn s)

let add_node s =
  let nb, graph = Graph.add_node s.graph in
  {s with graph; pos= nb}

module Operations = struct
  let identity : t -> t = Fn.id

  let next_port (f : t -> t) (s : t) : t =
    f {s with port= (s.port + 1) mod s.graph.max_conn}

  let prev_port (f : t -> t) (s : t) : t =
    f {s with port= (if s.port = 0 then s.graph.max_conn - 1 else s.port - 1)}

  let func (f : t -> t) (g : t -> t) (s : t) =
    let graph' = graph @@ f s in
    g {s with graph= (if Graph.n_components graph' > 1 then graph s else graph')}

  let if_positions_equal (f : t -> t) (g : t -> t) (h : t -> t) (k : t -> t)
      (l : t -> t) (s : t) : t =
    l (if pos (f s) = pos (g s) then h s else k s)

  let move (f : t -> t) (s : t) : t =
    f {s with pos= Option.value_map (selected s) ~default:s.pos ~f:Fn.id}

  let add (f : t -> t) (s : t) : t =
    if has_conn s && not (has_isolated s) then f @@ add_node s else f s

  let push (f : t -> t) (s : t) : t = f {s with conn= pos s :: conn s}

  let pop (f : t -> t) (s : t) : t =
    f
      { s with
        conn=
          ( match (List.tl @@ conn s, conn s, has_isolated s) with
          | rest, _, false ->
              Option.value_map rest ~default:[] ~f:Fn.id
          | _, [], true ->
              failwith "pop: isolated node has no way to connect with neighbors"
          | None, _, true ->
              failwith "pop: impossible"
          | Some rest, all, true ->
              if List.exists rest ~f:(( <> ) (pos s)) then rest else all ) }

  let connect (f : t -> t) (s : t) =
    f
      ( match (selected s, List.hd @@ conn s) with
      | Some _, _ | None, None ->
          s
      | None, Some nb ->
          {s with graph= Graph.add_edge s.port s.graph s.pos nb} )

  let last_found : Graph.t option ref = ref None

  let save (s : t) : t =
    last_found := Some s.graph ;
    s
end