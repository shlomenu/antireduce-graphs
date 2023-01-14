open Core
open Antireduce
open Exploration
open Program
include State
include Eval
module S = Yojson.Safe
module SU = Yojson.Safe.Util

let name_of_domain = "graph"

let all_primitives' j =
  all_primitives ~max_color:(SU.to_int @@ SU.member "max_color" j)

let parse_program' ?(primitives = all_primitives) ~max_color =
  Parser.parse_program @@ primitives ~max_color

let parse_program ?(primitives = all_primitives') j =
  Parser.parse_program (primitives j)

let parse_program_exn' ?(primitives = all_primitives) ~max_color =
  Fn.compose Util.value_exn (parse_program' ~primitives ~max_color)

let parse_program_exn ?(primitives = all_primitives') j =
  Fn.compose Util.value_exn (parse_program ~primitives j)

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir j =
  let max_color = SU.to_int @@ SU.member "max_color" j in
  let apply_to_state f =
    Apply
      ( Primitive {name= "save"; ty= graph_transform}
      , Apply (f, Primitive {name= "initial"; ty= graph_state}) )
  in
  let retrieve_result () = Util.value_exn !last_found in
  explore ~exploration_timeout ~eval_timeout ~attempts ~dsl ~representations_dir
    ~apply_to_state ~evaluate:(evaluate ~max_color) ~retrieve_result
    ~nontrivial:(fun g -> Map.length g.nodes > 1)
    ~parse:(parse_program_exn' ~max_color)
    ~request:graph_transform ~yojson_of_output:yojson_of_graph
    ~key_of_output:traversal ~yojson_of_key:Traversal.yojson_of_t
    ~key_of_yojson:Traversal.t_of_yojson
    (module Traversal)
