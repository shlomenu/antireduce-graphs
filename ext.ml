open Core
open Antireduce
module SU = Yojson.Safe.Util

let name_of_domain = "graph"

let parse_program ?(primitives = Eval.all_primitives) =
  Parser.parse_program primitives

let parse_stitch_invention ?(primitives = Eval.all_primitives) =
  Parser.parse_stitch_invention primitives

let parse_program_exn ?(primitives = Eval.all_primitives) =
  Parser.parse_program_exn primitives

let parse_stitch_invention_exn ?(primitives = Eval.all_primitives) =
  Parser.parse_stitch_invention_exn primitives

let apply_to_state (f : Program.t) : Program.t =
  Apply
    ( Primitive {name= "save"; ty= Eval.graph_transform}
    , Apply (f, Primitive {name= "initial"; ty= Eval.graph_state}) )

let retrieve_result () = Util.value_exn !State.Operations.last_found

let nontrivial g = Graph.size g > 1 && Graph.n_components g = 1

let explore ~exploration_timeout ~max_novel_representations ~program_size_limit
    ~eval_timeout ~attempts ~dsl ~representations_dir j =
  Exploration.multikey_explore ~exploration_timeout ~max_novel_representations
    ~program_size_limit ~eval_timeout ~attempts ~dsl ~representations_dir
    ~apply_to_state
    ~evaluate:(Eval.evaluate ~max_conn:(SU.to_int @@ SU.member "max_conn" j))
    ~retrieve_result ~nontrivial ~parse:parse_program_exn
    ~request:Eval.graph_transform ~yojson_of_output:Graph.yojson_of_t
    ~keys_of_output:(fun g ->
      let view = Graph.Frozen.of_graph g in
      (Graph.Key.of_frozen view, view) )
    ~yojson_of_primary_key:Graph.Key.yojson_of_t
    ~primary_key_of_yojson:Graph.Key.t_of_yojson
    ~yojson_of_secondary_key:Graph.Frozen.yojson_of_t
    ~secondary_key_of_yojson:Graph.Frozen.t_of_yojson
    ~equal_secondary_key:Graph.Morphism.has_iso
    (module Graph.Key)