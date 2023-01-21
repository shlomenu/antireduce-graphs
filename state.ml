open Core

type t =
  { graph: Graph.t
  ; loc: int
  ; color: int
  ; dir: Direction.t
  ; positions: int list
  ; colors: int list }
[@@deriving yojson, fields]

let empty ~max_color =
  { graph= Graph.empty ~max_color
  ; loc= 0
  ; color= 0
  ; dir= Forward
  ; positions= []
  ; colors= [] }

let neighbor_of_color s c =
  match dir s with
  | Forward ->
      Map.find s.graph.forward_edges (s.loc, c)
  | Backward ->
      Map.find s.graph.backward_edges (s.loc, c)

let selected s = neighbor_of_color s s.color

let equal s_1 s_2 =
  Traversal.equal (Graph.to_traversal s_1) (Graph.to_traversal s_2)

let of_graph g =
  {graph= g; loc= 0; color= 0; dir= Forward; positions= []; colors= []}
