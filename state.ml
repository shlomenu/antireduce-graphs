open Core

type t = {graph: Graph.t; pos: int; port: int} [@@deriving yojson, fields]

let empty ~max_conn = {graph= Graph.empty ~max_conn; pos= 0; port= 0}

let selected s = Option.map ~f:snd @@ Map.find s.graph.edges (s.pos, s.port)

let of_graph g = {graph= g; pos= 0; port= 0}
