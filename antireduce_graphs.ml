open Core
open Antireduce
open Program
include State
include Eval

let name_of_domain = "graph"

let prededup_frontier_entry_to_traversal c = traversal c.output

let parse_program' ~max_color =
  Parser.parse_program @@ initial_primitives ~max_color

let parse_program j =
  parse_program' ~max_color:(SU.to_int @@ SU.member "max_color" j)

let parse_program_exn' ~max_color =
  Fn.compose Util.value_exn (parse_program' ~max_color)

let parse_program_exn j = Fn.compose Util.value_exn (parse_program j)

let find_duplicates' ~max_color dir =
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
                match parse_program' ~max_color original with
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
       prededup_frontier_entry_to_traversal priority

let find_duplicates dir j =
  find_duplicates' ~max_color:(SU.to_int @@ SU.member "max_color" j) dir

let execute_and_save ~timeout ?(attempts = 1) ~dsl j =
  let max_color = SU.to_int @@ SU.member "max_color" j in
  let default_program =
    Abstraction
      (Apply
         ( Apply
             ( Hashtbl.find_exn (initial_primitives ~max_color) "add"
             , Hashtbl.find_exn (initial_primitives ~max_color) "identity" )
         , Index 0 ) )
  in
  let default_output () = (add Fn.id @@ initial_state ~max_color).graph in
  let postprocess_output out =
    if Hashtbl.length out.graph.nodes = 1 then
      (reset_color (add Fn.id) out).graph
    else out.graph
  in
  execute_and_save ~timeout ~attempts ~dsl ~default_program ~default_output
    ~evaluate:(evaluate ~max_color) ~postprocess_output
    ~yojson_of_output:yojson_of_graph ~request:graph_transform j
