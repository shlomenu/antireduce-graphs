open Core

type t = {graph: Graph.t; pos: int; port: int; dir: Direction.t}
[@@deriving yojson, fields]

let empty ~max_conn =
  {graph= Graph.empty ~max_conn; pos= 0; port= 0; dir= Forward}

let neighbor_of_port s port =
  match dir s with
  | Forward ->
      Option.map ~f:snd @@ Map.find s.graph.forward_edges (s.pos, port)
  | Backward ->
      Option.map ~f:snd @@ Map.find s.graph.backward_edges (s.pos, port)

let selected s = neighbor_of_port s s.port

let of_graph g = {graph= g; pos= 0; port= 0; dir= Forward}
