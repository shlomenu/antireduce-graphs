open Core
open Antireduce
open Yojson_util

type t =
  { edges: (int * int) Map.M(Util.IntPair).t
  ; next_id: int
  ; size: int
  ; max_conn: int
  ; n_components: int }
[@@deriving fields]

let yojson_of_edges =
  yojson_of_map Util.IntPair.yojson_of_t Util.IntPair.yojson_of_t

let yojson_of_t g =
  `Assoc
    [ ("edges", yojson_of_edges g.edges)
    ; ("next_id", yojson_of_int g.next_id)
    ; ("size", yojson_of_int g.size)
    ; ("max_conn", `Int g.max_conn) ]

let edges_of_yojson : Yojson.Safe.t -> (int * int) Map.M(Util.IntPair).t =
  map_of_yojson
    (module Util.IntPair)
    Util.IntPair.t_of_yojson Util.IntPair.t_of_yojson

let t_of_yojson = function
  | `Assoc
      [ ("edges", j_edges)
      ; ("next_id", `Int next_id)
      ; ("size", `Int size)
      ; ("max_conn", `Int max_conn) ] ->
      {edges= edges_of_yojson j_edges; next_id; size; max_conn; n_components= 1}
  | _ ->
      failwith "Graph.t_of_yojson: corrupted graph"

let add_node g =
  ( next_id g
  , { g with
      next_id= next_id g + 1
    ; size= size g + 1
    ; n_components= n_components g + 1 } )

(* Assumes that if the node has multiple components, then a new edge will connect them.
    This invariant is enforced by the design of operations in the State module. *)
let add_edge port g cursor neighbor =
  if
    (Option.is_some @@ Map.find g.edges (cursor, port))
    || (Option.is_some @@ Map.find g.edges (neighbor, port))
    || cursor = neighbor || cursor < 0
    || cursor >= next_id g
    || neighbor < 0
    || neighbor >= next_id g
  then g
  else
    { g with
      edges=
        Map.add_exn g.edges ~key:(cursor, port) ~data:(next_id g, neighbor)
        |> Map.add_exn ~key:(neighbor, port) ~data:(next_id g, cursor)
    ; next_id= next_id g + 1
    ; n_components=
        ( match n_components g with
        | 1 | 2 ->
            1
        | _ ->
            failwith "add_edge: invalid number of connected components" ) }

let empty ~max_conn =
  snd
  @@ add_node
       { edges= Map.empty (module Util.IntPair)
       ; next_id= 0
       ; size= 0
       ; max_conn
       ; n_components= 0 }

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

  let nodes = Map.keys

  let of_graph g =
    List.fold (Map.to_alist g.edges) ~init:Int.Map.empty
      ~f:(fun view' ((n_1, _), (_, n_2)) ->
        Map.update view' n_1 ~f:(function
          | Some nbs ->
              Set.add nbs n_2
          | None ->
              Set.singleton (module Int) n_2 )
        |> Fn.flip Map.update n_2 ~f:(function
             | Some nbs ->
                 Set.add nbs n_1
             | None ->
                 Set.singleton (module Int) n_1 ) )

  let neighbors_exn = Map.find_exn

  let connected view n_1 n_2 = Fn.flip Set.mem n_2 @@ Map.find_exn view n_1

  let degree view n = Set.length @@ neighbors_exn view n

  let degrees view =
    List.sort ~compare @@ List.map ~f:(degree view) @@ nodes view

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

  let nodes_1 morphism = Frozen.nodes (view_1 morphism)

  let nodes_2 morphism = Frozen.nodes (view_2 morphism)

  let of_views ~view_1 ~view_2 =
    assert (Frozen.size view_1 = Frozen.size view_2) ;
    let nbs_in_frontier =
      Frozen.nodes view_1
      |> List.map ~f:(fun i -> (i, 0))
      |> Map.of_alist_exn (module Int)
    in
    let nbs_in_non_frontier view =
      Frozen.nodes view
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
        nodes_2 morphism

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
      nodes_1 morphism
      |> List.map ~f:(fun i -> (i, Frozen.degree (view_1 morphism) i))
      |> List.fold ~init:(-1, Int.min_value) ~f:(fun a b ->
             if snd b > snd a then b else a )
      |> fst
    in
    let rec go
        ?(excluded = Set.remove (Int.Set.of_list @@ nodes_1 morphism) root)
        ?(included = Int.Set.singleton root) bfs_tree_rev =
      if not (Set.is_empty excluded) then
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
          ~excluded:
            (List.fold level ~init:excluded ~f:(fun excluded' n ->
                 Set.remove excluded' n ) )
          ~included:
            (List.fold level ~init:included ~f:(fun included' n ->
                 Set.add included' n ) )
          (level :: bfs_tree_rev)
      else bfs_tree_rev
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