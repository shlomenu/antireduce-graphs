open Core
open Antireduce
open Yojson_util

type t =
  { size: int
  ; forward_edges: int Map.M(Util.IntPair).t
  ; backward_edges: int Map.M(Util.IntPair).t
  ; max_conn: int }
[@@deriving fields]

let yojson_of_edges = yojson_of_map Util.IntPair.yojson_of_t yojson_of_int

let yojson_of_t g =
  `Assoc
    [ ("size", yojson_of_int g.size)
    ; ("forward_edges", yojson_of_edges g.forward_edges)
    ; ("backward_edges", yojson_of_edges g.backward_edges)
    ; ("max_conn", `Int g.max_conn) ]

let edges_of_yojson : Yojson.Safe.t -> int Map.M(Util.IntPair).t =
  map_of_yojson (module Util.IntPair) Util.IntPair.t_of_yojson int_of_yojson

let t_of_yojson = function
  | `Assoc
      [ ("size", `Int size)
      ; ("forward_edges", j_forward_edges)
      ; ("backward_edges", j_backward_edges)
      ; ("max_conn", `Int max_conn) ] ->
      { size
      ; forward_edges= edges_of_yojson j_forward_edges
      ; backward_edges= edges_of_yojson j_backward_edges
      ; max_conn }
  | _ ->
      failwith "Graph.t_of_yojson: corrupted graph"

let add_node g = (size g, {g with size= size g + 1})

let add_edge dir port g cursor neighbor =
  if
    cursor = neighbor || cursor < 0
    || cursor >= size g
    || neighbor < 0
    || neighbor >= size g
  then g
  else
    let cursor_edges, neighbor_edges =
      match dir with
      | Direction.Forward ->
          (g.forward_edges, g.backward_edges)
      | Direction.Backward ->
          (g.backward_edges, g.forward_edges)
    in
    if
      (Option.is_some @@ Map.find cursor_edges (cursor, port))
      && (Option.is_some @@ Map.find neighbor_edges (neighbor, port))
    then g
    else
      let cursor_edges =
        Map.add_exn cursor_edges ~key:(cursor, port) ~data:neighbor
      in
      let neighbor_edges =
        Map.add_exn neighbor_edges ~key:(neighbor, port) ~data:cursor
      in
      let forward_edges, backward_edges =
        match dir with
        | Forward ->
            (cursor_edges, neighbor_edges)
        | Backward ->
            (neighbor_edges, cursor_edges)
      in
      {g with forward_edges; backward_edges}

let empty ~max_conn =
  snd
  @@ add_node
       { size= 0
       ; forward_edges= Map.empty (module Util.IntPair)
       ; backward_edges= Map.empty (module Util.IntPair)
       ; max_conn }

module Frozen = struct
  type t = Set.M(Int).t Int.Map.t

  let yojson_of_t : t -> Yojson.Safe.t =
    Yojson_util.yojson_of_map yojson_of_int
      (Fn.compose (yojson_of_list yojson_of_int) Set.to_list)

  let t_of_yojson : Yojson.Safe.t -> t =
    Yojson_util.map_of_yojson
      (module Int)
      int_of_yojson
      (Fn.compose Int.Set.of_list (list_of_yojson int_of_yojson))

  let size = Map.length

  let of_graph g =
    let process view' ((n_1, _), n_2) =
      Map.update view' n_1 ~f:(function
        | Some nbs ->
            Set.add nbs n_2
        | None ->
            Set.singleton (module Int) n_2 )
      |> Fn.flip Map.update n_2 ~f:(function
           | Some nbs ->
               Set.add nbs n_1
           | None ->
               Set.singleton (module Int) n_1 )
    in
    let view =
      List.fold (Map.to_alist g.forward_edges) ~init:Int.Map.empty ~f:process
    in
    List.fold (Map.to_alist g.backward_edges) ~init:view ~f:process

  let is_node view n = n >= 0 && n < size view

  let is_node_check view n =
    if not (is_node view n) then
      raise
        (Not_found_s (Sexp.of_string @@ Format.sprintf "%i > %i" n @@ size view))

  let neighbors_exn view n = is_node_check view n ; Map.find_exn view n

  let connected view n_1 n_2 =
    is_node_check view n_1 ;
    is_node_check view n_2 ;
    Fn.flip Set.mem n_2 @@ Map.find_exn view n_1

  let degree view n = Set.length @@ neighbors_exn view n

  let degrees view =
    List.sort ~compare @@ List.map ~f:(degree view) @@ List.range 0 @@ size view

  let equal_deg_hist view_1 view_2 =
    List.equal equal (degrees view_1) (degrees view_2)
end

module Key = struct
  module T = struct
    type t = int * int list [@@deriving equal, compare, sexp_of, hash, yojson]
  end

  include T
  include Comparator.Make (T)

  let of_frozen view = (Frozen.size view, Frozen.degrees view)
end

module Morphism = struct
  type t =
    { view_1: Frozen.t
    ; view_2: Frozen.t
    ; m_1: int Int.Map.t
    ; m_2: int Int.Map.t
    ; mapped_1: Int.Set.t
    ; mapped_2: Int.Set.t
    ; frontier_1: Int.Set.t
    ; frontier_2: Int.Set.t
    ; nbs_in_frontier_1: int Int.Map.t
    ; nbs_in_frontier_2: int Int.Map.t
    ; non_frontier_1: Int.Set.t
    ; non_frontier_2: Int.Set.t
    ; nbs_in_non_frontier_1: int Int.Map.t
    ; nbs_in_non_frontier_2: int Int.Map.t }
  [@@deriving fields]

  let size morphism = Map.length @@ view_1 morphism

  let all_nodes = Fn.compose (List.range 0) size

  let of_views ~view_1 ~view_2 =
    assert (Frozen.size view_1 = Frozen.size view_2) ;
    let nbs_in_frontier =
      Frozen.size view_1 |> List.range 0
      |> List.map ~f:(fun i -> (i, 0))
      |> Map.of_alist_exn (module Int)
    in
    let nbs_in_non_frontier view =
      Frozen.size view |> List.range 0
      |> List.map ~f:(fun i -> (i, Frozen.degree view i))
      |> Map.of_alist_exn (module Int)
    in
    { view_1
    ; view_2
    ; m_1= Int.Map.empty
    ; m_2= Int.Map.empty
    ; mapped_1= Int.Set.empty
    ; mapped_2= Int.Set.empty
    ; frontier_1= Int.Set.empty
    ; frontier_2= Int.Set.empty
    ; nbs_in_frontier_1= nbs_in_frontier
    ; nbs_in_frontier_2= nbs_in_frontier
    ; non_frontier_1= Int.Set.empty
    ; non_frontier_2= Int.Set.empty
    ; nbs_in_non_frontier_1= nbs_in_non_frontier view_1
    ; nbs_in_non_frontier_2= nbs_in_non_frontier view_2 }

  let neighbors_1 morphism n_1 = Frozen.neighbors_exn (view_1 morphism) n_1

  let neighbors_2 morphism n_2 = Frozen.neighbors_exn (view_2 morphism) n_2

  let fold_neighbors_1 morphism n_1 = Set.fold @@ neighbors_1 morphism n_1

  let fold_neighbors_2 morphism n_2 = Set.fold @@ neighbors_2 morphism n_2

  let candidates morphism ~n_1 =
    match
      neighbors_1 morphism n_1 |> Set.inter (mapped_1 morphism) |> Set.choose
    with
    | Some nb_1 ->
        Map.find_exn (m_1 morphism) nb_1
        |> neighbors_2 morphism
        |> Fn.flip Set.diff (mapped_2 morphism)
        |> Set.to_list
    | None ->
        size morphism |> List.range 0

  let consistent morphism ~n_1 ~n_2 =
    if
      neighbors_1 morphism n_1
      |> Set.inter (mapped_1 morphism)
      |> Set.map (module Int) ~f:(Map.find_exn (m_1 morphism))
      |> Set.for_all ~f:(Frozen.connected (view_2 morphism) n_2)
      && neighbors_2 morphism n_2
         |> Set.inter (mapped_2 morphism)
         |> Set.map (module Int) ~f:(Map.find_exn (m_2 morphism))
         |> Set.for_all ~f:(Frozen.connected (view_1 morphism) n_1)
    then
      Some
        { morphism with
          m_1= Map.add_exn (m_1 morphism) ~key:n_1 ~data:n_2
        ; m_2= Map.add_exn (m_2 morphism) ~key:n_2 ~data:n_1
        ; mapped_1= Set.add (mapped_1 morphism) n_1
        ; mapped_2= Set.add (mapped_2 morphism) n_2 }
    else None

  let cuttable morphism ~n_1 ~n_2 =
    if
      Map.find_exn (nbs_in_frontier_1 morphism) n_1
      = Map.find_exn (nbs_in_frontier_2 morphism) n_2
      && Map.find_exn (nbs_in_non_frontier_1 morphism) n_1
         = Map.find_exn (nbs_in_non_frontier_2 morphism) n_2
    then
      let unmapped_nbs_of_n_1 =
        Set.diff (neighbors_1 morphism n_1) (mapped_1 morphism)
      in
      let unmapped_nbs_of_n_2 =
        Set.diff (neighbors_2 morphism n_2) (mapped_2 morphism)
      in
      let non_frontier_nbs_of_n_1 =
        Set.diff unmapped_nbs_of_n_1 (frontier_1 morphism)
      in
      let non_frontier_nbs_of_n_2 =
        Set.diff unmapped_nbs_of_n_2 (frontier_2 morphism)
      in
      Some
        { morphism with
          frontier_1=
            Set.union unmapped_nbs_of_n_1 (Set.remove (frontier_1 morphism) n_1)
        ; frontier_2=
            Set.union unmapped_nbs_of_n_2 (Set.remove (frontier_2 morphism) n_2)
        ; nbs_in_frontier_1=
            ( fold_neighbors_1 morphism n_1 ~init:(nbs_in_frontier_1 morphism)
                ~f:(fun nbs_in_frontier_1' nb ->
                  Map.change nbs_in_frontier_1' nb
                    ~f:(Option.map ~f:(fun c -> max 0 (c - 1))) )
            |> fun nbs_in_frontier_1' ->
            Set.fold non_frontier_nbs_of_n_1 ~init:nbs_in_frontier_1'
              ~f:(fun nbs_in_frontier_1'' nb ->
                fold_neighbors_1 morphism nb ~init:nbs_in_frontier_1''
                  ~f:(fun nbs_in_frontier_1''' nb' ->
                    Map.change nbs_in_frontier_1''' nb'
                      ~f:(Option.map ~f:(( + ) 1)) ) ) )
        ; nbs_in_frontier_2=
            ( fold_neighbors_2 morphism n_2 ~init:(nbs_in_frontier_2 morphism)
                ~f:(fun nbs_in_frontier_2' nb ->
                  Map.change nbs_in_frontier_2' nb
                    ~f:(Option.map ~f:(fun c -> max 0 (c - 1))) )
            |> fun nbs_in_frontier_2' ->
            Set.fold non_frontier_nbs_of_n_2 ~init:nbs_in_frontier_2'
              ~f:(fun nbs_in_frontier_2'' nb ->
                fold_neighbors_2 morphism nb ~init:nbs_in_frontier_2''
                  ~f:(fun nbs_in_frontier_2''' nb' ->
                    Map.change nbs_in_frontier_2''' nb'
                      ~f:(Option.map ~f:(( + ) 1)) ) ) )
        ; nbs_in_non_frontier_1=
            Set.fold non_frontier_nbs_of_n_1
              ~init:(nbs_in_non_frontier_1 morphism)
              ~f:(fun nbs_in_non_frontier_1' nb ->
                fold_neighbors_1 morphism nb ~init:nbs_in_non_frontier_1'
                  ~f:(fun nbs_in_non_frontier_1'' nb' ->
                    Map.change nbs_in_non_frontier_1'' nb'
                      ~f:(Option.map ~f:(fun c -> max 0 (c - 1))) ) )
        ; nbs_in_non_frontier_2=
            Set.fold non_frontier_nbs_of_n_2
              ~init:(nbs_in_non_frontier_2 morphism)
              ~f:(fun nbs_in_non_frontier_2' nb ->
                fold_neighbors_2 morphism nb ~init:nbs_in_non_frontier_2'
                  ~f:(fun nbs_in_non_frontier_2'' nb' ->
                    Map.change nbs_in_non_frontier_2'' nb'
                      ~f:(Option.map ~f:(fun c -> max 0 (c - 1))) ) ) }
    else None

  let feasible morphism ~n_1 ~n_2 =
    Option.bind ~f:(cuttable ~n_1 ~n_2) @@ consistent morphism ~n_1 ~n_2

  let to_bfs_tree morphism =
    let root =
      all_nodes morphism
      |> List.map ~f:(fun i -> (i, Frozen.degree (view_1 morphism) i))
      |> List.fold ~init:(-1, Int.min_value) ~f:(fun a b ->
             if snd b > snd a then b else a )
      |> fst
    in
    let rec go ?(included = Int.Set.singleton root) bfs_tree_rev =
      let level =
        List.hd_exn bfs_tree_rev
        |> List.fold ~init:(Int.Map.empty, Int.Set.empty)
             ~f:(fun (included_nbs, level) included_node ->
               let frontier_nodes =
                 Set.diff (neighbors_1 morphism included_node) included
               in
               ( Set.fold frontier_nodes ~init:included_nbs
                   ~f:(fun included_nbs' frontier_node ->
                     Map.update included_nbs' frontier_node ~f:(function
                       | Some nbs ->
                           Set.add nbs included_node
                       | None ->
                           Int.Set.singleton included_node ) )
               , Set.union level frontier_nodes ) )
        |> fun (included_nbs, level) ->
        let rec go' included' included_nbs' = function
          | _ :: _ as ns ->
              List.sort ns ~compare:(fun x y ->
                  let c =
                    -compare
                       (Set.length @@ Map.find_exn included_nbs' x)
                       (Set.length @@ Map.find_exn included_nbs' y)
                  in
                  if c <> 0 then c
                  else
                    -compare
                       (Set.length @@ Map.find_exn (view_1 morphism) x)
                       (Set.length @@ Map.find_exn (view_1 morphism) y) )
              |> Fn.flip List.split_n 1
              |> fun (ft, rest) ->
              let ft = List.hd_exn ft in
              ft
              :: go' (Set.add included' ft)
                   ( Set.diff (neighbors_1 morphism ft) included'
                   |> Set.fold ~init:included_nbs'
                        ~f:(fun included_nbs'' nonincluded_ft_nb ->
                          Map.change included_nbs'' nonincluded_ft_nb
                            ~f:(Option.map ~f:(Fn.flip Set.add ft)) ) )
                   rest
          | [] ->
              []
        in
        go' included included_nbs @@ Set.to_list level
      in
      go
        ~included:
          (List.fold level ~init:included ~f:(fun included' n ->
               Set.add included' n ) )
        (level :: bfs_tree_rev)
    in
    List.concat @@ List.rev @@ go [[root]]

  let has_iso view_1 view_2 =
    let[@tailcall] rec go morphism = function
      | n_1 :: rest ->
          candidates morphism ~n_1
          |> List.fold ~init:false ~f:(fun found n_2 ->
                 found
                 || feasible morphism ~n_1 ~n_2
                    |> Option.value_map ~default:false ~f:(Fn.flip go rest) )
      | [] ->
          true
    in
    let morphism = of_views ~view_1 ~view_2 in
    go morphism @@ to_bfs_tree morphism
end