open Core
open Antireduce
open Program
open Transforms
include State
include Eval

let name_of_domain = "graph"

let candidate_transform_to_traversal c = traversal c.output

let parse_program = Parser.parse_program initial_primitives

let parse_program_exn = Fn.compose Util.value_exn parse_program

let find_duplicates dir =
  let priority c_1 c_2 = compare c_1.program_size c_2.program_size in
  Caml.Sys.readdir dir
  |> Array.filter_map ~f:(fun filename ->
         let path = Filename.concat dir filename in
         let j = S.from_file path in
         Some
           { output=
               initial_state_of_graph @@ graph_of_yojson @@ SU.member "output" j
           ; program_size=
               (let original = SU.to_string @@ SU.member "original" j in
                match parse_program original with
                | Some p ->
                    size_of_program p
                | None ->
                    failwith
                    @@ Format.sprintf "could not parse graph domain program: %s"
                         original )
           ; filename
           ; path } )
  |> Array.to_list
  |> verbose_duplicates
       (module Traversal)
       candidate_transform_to_traversal priority

let execute_and_save ~timeout ?(attempts = 1) ~dsl j =
  let max_node_color = SU.to_int @@ SU.member "max_node_color" j in
  let default_program =
    Abstraction
      (Apply
         ( Apply
             ( Hashtbl.find_exn initial_primitives "add"
             , Hashtbl.find_exn initial_primitives "identity" )
         , Index 0 ) )
  in
  let default_output () = (add Fn.id @@ initial_state ~max_node_color).graph in
  let postprocess_output out =
    if Hashtbl.length out.graph.nodes = 1 then
      (reset_color (add Fn.id) out).graph
    else out.graph
  in
  execute_and_save ~timeout ~attempts ~dsl ~default_program ~default_output
    ~evaluate:(evaluate ~max_node_color) ~postprocess_output
    ~yojson_of_output:yojson_of_graph ~transform_type:graph_transform j
