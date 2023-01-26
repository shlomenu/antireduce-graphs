open Core
open Antireduce
include State
include Eval
module S = Yojson.Safe
module SU = Yojson.Safe.Util

let name_of_domain = "graph"

let parse_program ?(primitives = all_primitives) =
  Parser.parse_program primitives

let parse_stitch_invention ?(primitives = all_primitives) =
  Parser.parse_stitch_invention primitives

let parse_program_exn ?(primitives = all_primitives) =
  Parser.parse_program_exn primitives

let parse_stitch_invention_exn ?(primitives = all_primitives) =
  Parser.parse_stitch_invention_exn primitives

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir j =
  let max_conn = SU.to_int @@ SU.member "max_conn" j in
  let retrieve_result () = Util.value_exn !Operations.last_found in
  Exploration.multikey_explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir
    ~apply_to_state:(fun f ->
      Apply
        ( Primitive {name= "save"; ty= graph_transform}
        , Apply (f, Primitive {name= "initial"; ty= graph_state}) ) )
    ~evaluate:(evaluate ~max_conn) ~retrieve_result
    ~nontrivial:(fun g -> Graph.size g > 1)
    ~parse:parse_program_exn ~request:graph_transform
    ~yojson_of_output:Graph.yojson_of_t
    ~keys_of_output:(fun g ->
      let view = Graph.Frozen.of_graph g in
      (Graph.Key.of_frozen view, view) )
    ~yojson_of_primary_key:Graph.Key.yojson_of_t
    ~primary_key_of_yojson:Graph.Key.t_of_yojson
    ~yojson_of_secondary_key:Graph.Frozen.yojson_of_t
    ~secondary_key_of_yojson:Graph.Frozen.t_of_yojson
    ~equal_secondary_key:Graph.Morphism.has_iso
    (module Graph.Key)