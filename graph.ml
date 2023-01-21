open Core
open Antireduce
open Yojson_util

type t =
  { nodes: int Map.M(Int).t
  ; forward_edges: int Map.M(Util.IntPair).t
  ; backward_edges: int Map.M(Util.IntPair).t
  ; max_color: int }
[@@deriving fields]

let yojson_of_nodes = yojson_of_map yojson_of_int yojson_of_int

let yojson_of_edges = yojson_of_map Util.IntPair.yojson_of_t yojson_of_int

let yojson_of_t g =
  `Assoc
    [ ("nodes", yojson_of_nodes g.nodes)
    ; ("forward_edges", yojson_of_edges g.forward_edges)
    ; ("backward_edges", yojson_of_edges g.backward_edges)
    ; ("max_color", `Int g.max_color) ]

let nodes_of_yojson : Yojson.Safe.t -> int Map.M(Int).t =
  map_of_yojson (module Int) int_of_yojson int_of_yojson

let edges_of_yojson : Yojson.Safe.t -> int Map.M(Util.IntPair).t =
  map_of_yojson (module Util.IntPair) Util.IntPair.t_of_yojson int_of_yojson

let t_of_yojson = function
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
      | Direction.Forward ->
          (g.forward_edges, g.backward_edges)
      | Direction.Backward ->
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

let empty ~max_color =
  snd
  @@ Fn.flip add_node 0
       { nodes= Map.empty (module Int)
       ; forward_edges= Map.empty (module Util.IntPair)
       ; backward_edges= Map.empty (module Util.IntPair)
       ; max_color }

let to_traversal g : Traversal.t =
  let visited = Hashtbl.create (module Int) in
  Hashtbl.add_exn visited ~key:0 ~data:0 ;
  let rec go dir cursor n_visited traversal =
    max_color g |> List.range 0
    |> List.map ~f:(fun color ->
           ( color
           , match dir with
             | Direction.Forward ->
                 Map.find g.forward_edges (cursor, color)
             | Direction.Backward ->
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
  let n_visited, traversal = go Direction.Forward 0 1 [] in
  List.rev @@ snd @@ go Direction.Backward 0 n_visited traversal
