open Core
open Antireduce
open Util.Yojson_util

type direction = Forward | Backward [@@deriving yojson]

type graph =
  { nodes: (int, int) Hashtbl.t
  ; forward_edges: (int, int option Array.t) Hashtbl.t
  ; backward_edges: (int, int option Array.t) Hashtbl.t
  ; max_color: int }

let yojson_of_nodes = yojson_of_hashtbl yojson_of_int yojson_of_int

let yojson_of_edges =
  yojson_of_hashtbl yojson_of_int
    (yojson_of_array (yojson_of_option yojson_of_int))

let yojson_of_graph g =
  `Assoc
    [ ("nodes", yojson_of_nodes g.nodes)
    ; ("forward_edges", yojson_of_edges g.forward_edges)
    ; ("backward_edges", yojson_of_edges g.backward_edges)
    ; ("max_color", `Int g.max_color) ]

let nodes_of_yojson = hashtbl_of_yojson (module Int) int_of_yojson int_of_yojson

let edges_of_yojson =
  hashtbl_of_yojson
    (module Int)
    int_of_yojson
    (array_of_yojson (option_of_yojson int_of_yojson))

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
    let msg =
      Printf.sprintf "add_node: color (%d) is not below the threshold (%d)"
        color g.max_color
    in
    failwith msg
  else
    let node = Hashtbl.length g.nodes in
    Hashtbl.add_exn g.nodes ~key:node ~data:color ;
    Hashtbl.add_exn g.forward_edges ~key:node
      ~data:(Array.create ~len:g.max_color None) ;
    Hashtbl.add_exn g.backward_edges ~key:node
      ~data:(Array.create ~len:g.max_color None) ;
    node

let add_edge ~dir g cursor neighbor =
  if cursor <> neighbor then
    let cursor_edges =
      match dir with
      | Forward ->
          Hashtbl.find_exn g.forward_edges cursor
      | Backward ->
          Hashtbl.find_exn g.backward_edges cursor
    in
    let neighbor_edges =
      match dir with
      | Forward ->
          Hashtbl.find_exn g.backward_edges neighbor
      | Backward ->
          Hashtbl.find_exn g.forward_edges neighbor
    in
    let cursor_color = Hashtbl.find_exn g.nodes cursor in
    let neighbor_color = Hashtbl.find_exn g.nodes neighbor in
    if
      Option.is_none cursor_edges.(neighbor_color)
      && Option.is_none neighbor_edges.(cursor_color)
    then (
      cursor_edges.(neighbor_color) <- Some neighbor ;
      neighbor_edges.(cursor_color) <- Some cursor )

let initial_graph ~max_color =
  let g =
    { nodes= Hashtbl.create (module Int)
    ; forward_edges= Hashtbl.create (module Int)
    ; backward_edges= Hashtbl.create (module Int)
    ; max_color }
  in
  ignore (add_node g 0 : int) ;
  g

type state =
  { graph: graph
  ; mutable cursor: int
  ; mutable color: int
  ; mutable dir: direction
  ; positions: int list
  ; colors: int list }
[@@deriving yojson]

let initial_state ~max_color =
  { graph= initial_graph ~max_color
  ; cursor= 0
  ; color= 0
  ; dir= Forward
  ; positions= []
  ; colors= [] }

let cursor_neighbors s =
  match s.dir with
  | Forward ->
      Hashtbl.find_exn s.graph.forward_edges s.cursor
  | Backward ->
      Hashtbl.find_exn s.graph.backward_edges s.cursor

module Traversal = struct
  type t = Util.IntPair.t option list
  [@@deriving equal, compare, sexp_of, hash, yojson]
end

let traversal s : Traversal.t =
  let visited = Hashtbl.create (module Int) in
  Hashtbl.add_exn visited ~key:0 ~data:0 ;
  let rec go n_visited raw =
    cursor_neighbors s
    |> Array.mapi ~f:(fun color nb -> (color, nb))
    |> Array.fold ~init:(n_visited, raw) ~f:(fun (nv, r) (color, nb) ->
           match nb with
           | Some node_id ->
               if not @@ Hashtbl.mem visited node_id then (
                 s.cursor <- node_id ;
                 Hashtbl.add_exn visited ~key:node_id ~data:nv ;
                 go (nv + 1) (Some (nv, color) :: r) )
               else
                 let nv_prev = Hashtbl.find_exn visited node_id in
                 (nv, Some (nv - nv_prev, color) :: r)
           | None ->
               (nv, None :: r) )
  in
  s.cursor <- 0 ;
  s.color <- 0 ;
  s.dir <- Forward ;
  let n_visited, traversal = go 1 [] in
  s.cursor <- 0 ;
  s.color <- 0 ;
  s.dir <- Backward ;
  List.rev @@ snd @@ go n_visited traversal

let equal_state s_1 s_2 = Traversal.equal (traversal s_1) (traversal s_2)

let initial_state_of_graph graph =
  {graph; cursor= 0; color= 0; dir= Forward; positions= []; colors= []}

let reorient (f : state -> state) (s : state) : state =
  let reverse = function Forward -> Backward | Backward -> Forward in
  s.dir <- reverse s.dir ;
  f s

let next (f : state -> state) (s : state) : state =
  s.color <- (s.color + 1) mod s.graph.max_color ;
  f s

let set_color_under_cursor (f : state -> state) (s : state) : state =
  s.color <- Hashtbl.find_exn s.graph.nodes s.cursor ;
  f s

let reset_color (f : state -> state) (s : state) : state =
  s.color <- 0 ;
  f s

let reset_cursor (f : state -> state) (s : state) : state =
  s.cursor <- 0 ;
  f s

let traverse (f : state -> state) (s : state) : state =
  let neighbors = cursor_neighbors s in
  if Option.is_some neighbors.(s.color) then
    s.cursor <- Util.value_exn neighbors.(s.color) ;
  f s

let add (f : state -> state) (s : state) =
  let neighbors = cursor_neighbors s in
  if Option.is_none neighbors.(s.color) then
    add_edge ~dir:s.dir s.graph s.cursor @@ add_node s.graph s.color ;
  f s

let if_traversable (f : state -> state) (g : state -> state)
    (h : state -> state) (s : state) : state =
  let neighbors = cursor_neighbors s in
  if Option.is_some neighbors.(s.color) then f (g s) else f (h s)

let if_current (f : state -> state) (g : state -> state) (h : state -> state)
    (s : state) : state =
  if Hashtbl.find_exn s.graph.nodes s.cursor |> equal s.color then f (g s)
  else f (h s)

let connect (f : state -> state) (s : state) : state =
  let neighbors = cursor_neighbors s in
  ( if Option.is_none neighbors.(s.color) then
    match s.positions with
    | top :: _ ->
        add_edge ~dir:s.dir s.graph s.cursor top
    | [] ->
        () ) ;
  f s

let push_pos (f : state -> state) (s : state) : state =
  f {s with positions= s.cursor :: s.positions}

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
