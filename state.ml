open Core
open Antireduce
open Util.Yojson_util

type direction = Forward | Backward [@@deriving yojson]

type graph =
  { nodes: (Int.t, Int.t, Int.comparator_witness) Map.t
  ; forward_edges:
      (Util.OrdIntPair.t, Int.t, Util.OrdIntPair.comparator_witness) Map.t
  ; backward_edges:
      (Util.OrdIntPair.t, Int.t, Util.OrdIntPair.comparator_witness) Map.t
  ; max_color: int }

let yojson_of_nodes = yojson_of_map yojson_of_int yojson_of_int

let yojson_of_edges = yojson_of_map Util.OrdIntPair.yojson_of_t yojson_of_int

let yojson_of_graph g =
  `Assoc
    [ ("nodes", yojson_of_nodes g.nodes)
    ; ("forward_edges", yojson_of_edges g.forward_edges)
    ; ("backward_edges", yojson_of_edges g.backward_edges)
    ; ("max_color", `Int g.max_color) ]

let nodes_of_yojson = map_of_yojson (module Int) int_of_yojson int_of_yojson

let edges_of_yojson =
  map_of_yojson
    (module Util.OrdIntPair)
    Util.OrdIntPair.t_of_yojson int_of_yojson

let graph_of_yojson = function
  | `Assoc
      [ ("nodes", j_nodes)
      ; ("forward_edges", j_forward_edges)
      ; ("backward_edges", j_backward_edges)
      ; ("max_color", `Int max_color) ] ->
      { nodes= nodes_of_yojson j_nodes
      ; forward_edges= edges_of_yojson j_forward_edges
      ; backward_edges= edges_of_yojson j_backward_edges
      ; max_color }
  | _ ->
      failwith "corrupted graph"

let add_node g color =
  if color < 0 || color >= g.max_color then
    failwith
    @@ Printf.sprintf "add_node: color (%d) is not below the threshold (%d)"
         color g.max_color
  else
    let node = Map.length g.nodes in
    (node, {g with nodes= Map.add_exn g.nodes ~key:node ~data:color})

let add_edge dir g cursor neighbor =
  if
    cursor = neighbor
    || (not (Map.mem g.nodes cursor))
    || not (Map.mem g.nodes neighbor)
  then g
  else
    let cursor_edges, neighbor_edges =
      match dir with
      | Forward ->
          (g.forward_edges, g.backward_edges)
      | Backward ->
          (g.backward_edges, g.forward_edges)
    in
    let cursor_color = Map.find_exn g.nodes cursor in
    let neighbor_color = Map.find_exn g.nodes neighbor in
    if
      (Option.is_some @@ Map.find cursor_edges (cursor, neighbor_color))
      || (Option.is_some @@ Map.find neighbor_edges (neighbor, cursor_color))
    then g
    else
      let cursor_edges =
        Map.add_exn cursor_edges ~key:(cursor, neighbor_color) ~data:neighbor
      in
      let neighbor_edges =
        Map.add_exn neighbor_edges ~key:(neighbor, cursor_color) ~data:cursor
      in
      let forward_edges, backward_edges =
        match dir with
        | Forward ->
            (cursor_edges, neighbor_edges)
        | Backward ->
            (neighbor_edges, cursor_edges)
      in
      {g with forward_edges; backward_edges}

let initial_graph ~max_color =
  snd
  @@ Fn.flip add_node 0
       { nodes= Map.empty (module Int)
       ; forward_edges= Map.empty (module Util.OrdIntPair)
       ; backward_edges= Map.empty (module Util.OrdIntPair)
       ; max_color }

type state =
  { graph: graph
  ; loc: int
  ; color: int
  ; dir: direction
  ; positions: int list
  ; colors: int list }
[@@deriving yojson]

let initial_state ~max_color =
  { graph= initial_graph ~max_color
  ; loc= 0
  ; color= 0
  ; dir= Forward
  ; positions= []
  ; colors= [] }

let neighbor_of_color s c =
  match s.dir with
  | Forward ->
      Map.find s.graph.forward_edges (s.loc, c)
  | Backward ->
      Map.find s.graph.backward_edges (s.loc, c)

let selected s = neighbor_of_color s s.color

module Traversal = struct
  type t = Util.IntPair.t option list
  [@@deriving equal, compare, sexp_of, hash, yojson]
end

let traversal g : Traversal.t =
  let visited = Hashtbl.create (module Int) in
  Hashtbl.add_exn visited ~key:0 ~data:0 ;
  let rec go dir cursor n_visited traversal =
    List.range 0 g.max_color
    |> List.map ~f:(fun color ->
           ( color
           , match dir with
             | Forward ->
                 Map.find g.forward_edges (cursor, color)
             | Backward ->
                 Map.find g.backward_edges (cursor, color) ) )
    |> List.fold ~init:(n_visited, traversal) ~f:(fun (n, t) (color, nb) ->
           match nb with
           | Some node ->
               if not @@ Hashtbl.mem visited node then (
                 Hashtbl.add_exn visited ~key:node ~data:n ;
                 go dir node (n + 1) (Some (n, color) :: t) )
               else
                 let n_prev = Hashtbl.find_exn visited node in
                 (n, Some (n - n_prev, color) :: t)
           | None ->
               (n, None :: t) )
  in
  let n_visited, traversal = go Forward 0 1 [] in
  List.rev @@ snd @@ go Backward 0 n_visited traversal

let equal_state s_1 s_2 = Traversal.equal (traversal s_1) (traversal s_2)

let initial_state_of_graph graph =
  {graph; loc= 0; color= 0; dir= Forward; positions= []; colors= []}

let reorient (f : state -> state) (s : state) : state =
  let opposite = function Forward -> Backward | Backward -> Forward in
  f {s with dir= opposite s.dir}

let next (f : state -> state) (s : state) : state =
  f {s with color= (s.color + 1) mod s.graph.max_color}

let set_color_under_cursor (f : state -> state) (s : state) : state =
  f {s with color= Map.find_exn s.graph.nodes s.loc}

let reset_color (f : state -> state) (s : state) : state = f {s with color= 0}

let reset_cursor (f : state -> state) (s : state) : state = f {s with loc= 0}

let traverse (f : state -> state) (s : state) : state =
  f {s with loc= Option.value_map (selected s) ~default:s.loc ~f:Fn.id}

let add (f : state -> state) (s : state) =
  f
    { s with
      graph=
        ( if Option.is_none (selected s) then
          let nb, g' = add_node s.graph s.color in
          add_edge s.dir g' s.loc nb
        else s.graph ) }

let if_traversable (f : state -> state) (g : state -> state)
    (h : state -> state) (s : state) : state =
  if Option.is_some @@ selected s then f (g s) else f (h s)

let if_current (f : state -> state) (g : state -> state) (h : state -> state)
    (s : state) : state =
  if equal s.color @@ Map.find_exn s.graph.nodes s.loc then f (g s) else f (h s)

let connect (f : state -> state) (s : state) : state =
  f
    { s with
      graph=
        Option.value_map ~default:s.graph ~f:(add_edge s.dir s.graph s.loc)
        @@ List.hd s.positions }

let push_pos (f : state -> state) (s : state) : state =
  f {s with positions= s.loc :: s.positions}

let pop_pos (f : state -> state) (s : state) : state =
  f {s with positions= List.drop s.positions 1}

let push_color (f : state -> state) (s : state) : state =
  f {s with colors= s.color :: s.colors}

let pop_color (f : state -> state) (s : state) : state =
  f {s with colors= List.drop s.colors 1}

let for_i (i : int) (g : state -> state) (f : state -> state) (s : state) :
    state =
  f @@ List.fold (List.range 0 i) ~init:s ~f:(fun s' _ -> g s')

let pos_proc (g : state -> state) (f : state -> state) (s : state) : state =
  f {(g {s with positions= []}) with positions= s.positions}

let color_proc (g : state -> state) (f : state -> state) (s : state) : state =
  f {(g {s with colors= []}) with colors= s.colors}

let last_found : graph option ref = ref None

let save (s : state) : state =
  last_found := Some s.graph ;
  s

(*

    --- API rewrite, kept separate for backwards compatibility ---

   Some functions are simply renamed and some are obsolesced, but no name
   clashes are introduced.
*)

let identity : state -> state = Fn.id

let switch_direction = reorient

let select_next = next

let select_prev (f : state -> state) (s : state) : state =
  f {s with color= (if s.color = 0 then s.graph.max_color - 1 else s.color - 1)}

let read_color = set_color_under_cursor

let color_func (f : state -> state) (g : state -> state) (s : state) =
  g {(f s) with color= s.color}

let loc_func (f : state -> state) (g : state -> state) (s : state) : state =
  g {(f s) with loc= s.loc}

let dir_func (f : state -> state) (g : state -> state) (s : state) : state =
  g {(f s) with dir= s.dir}

let func (f : state -> state) (g : state -> state) (s : state) : state =
  g {(f s) with color= s.color; loc= s.loc; dir= s.dir}

let if_colors_equal (f : state -> state) (g : state -> state)
    (h : state -> state) (k : state -> state) (l : state -> state) (s : state) :
    state =
  l (if (f s).color = (g s).color then h s else k s)

let if_locs_equal (f : state -> state) (g : state -> state) (h : state -> state)
    (k : state -> state) (l : state -> state) (s : state) : state =
  l (if (f s).loc = (g s).loc then h s else k s)

let move_selected = traverse

let add_nb = add

let add_conn (f : state -> state) (g : state -> state) (h : state -> state)
    (s : state) : state =
  h {s with graph= add_edge s.dir s.graph (f s).loc (g s).loc}
