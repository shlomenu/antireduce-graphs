open Core
open Antireduce
open Type
open Program
open Dsl
open State

type graph_value =
  | Int of int
  | IntOp1 of (int -> int)
  | IntOp2 of (int -> int -> int)
  | State of state
  | Transform of (state -> state)
  | App1 of ((state -> state) -> state -> state)
  | App2 of ((state -> state) -> (state -> state) -> state -> state)
  | App3 of
      (   (state -> state)
       -> (state -> state)
       -> (state -> state)
       -> state
       -> state )
  | For of (int -> (state -> state) -> (state -> state) -> state -> state)

let graph_int = kind "int" []

let graph_int_binop = graph_int @> graph_int @> graph_int

let graph_state = kind "graph_state" []

let graph_transform = graph_state @> graph_state

let graph_app1 = graph_transform @> graph_state @> graph_state

let graph_app2 =
  graph_transform @> graph_transform @> graph_state @> graph_state

let graph_app3 =
  graph_transform @> graph_transform @> graph_transform @> graph_state
  @> graph_state

let graph_for =
  graph_int @> graph_transform @> graph_transform @> graph_state @> graph_state

let graph_values ~max_node_color =
  Hashtbl.of_alist_exn (module String)
  @@ ( List.range 0 @@ max 11 max_node_color
     |> List.map ~f:(fun i -> (string_of_int i, Int i)) )
  @ [ ("plus", IntOp2 ( + ))
    ; ("mult", IntOp2 ( * ))
    ; ("initial", State (initial_state ~max_node_color))
    ; ("identity", Transform identity)
    ; ("reorient", App1 reorient)
    ; ("next", App1 next)
    ; ("set_color_under_cursor", App1 set_color_under_cursor)
    ; ("reset_color", App1 reset_color)
    ; ("reset_cursor", App1 reset_cursor)
    ; ("traverse", App1 traverse)
    ; ("add", App1 add)
    ; ("if_traversable", App3 if_traversable)
    ; ("if_current", App3 if_current)
    ; ("connect", App1 connect)
    ; ("push_pos", App1 push_pos)
    ; ("pop_pos", App1 pop_pos)
    ; ("push_color", App1 push_color)
    ; ("pop_color", App1 pop_color)
    ; ("for_i", For for_i)
    ; ("pos_proc", App2 pos_proc)
    ; ("color_proc", App2 color_proc) ]

let lookup ~max_node_color = Hashtbl.find_exn @@ graph_values ~max_node_color

let eval gv_1 gv_2 =
  match (gv_1, gv_2) with
  | IntOp2 op, Int i ->
      IntOp1 (op i)
  | IntOp2 _, _ ->
      failwith "Graphs.evaluator: apply of integer op to non-integer"
  | IntOp1 op, Int i ->
      Int (op i)
  | IntOp1 _, _ ->
      failwith "Graphs.evaluator: apply of integer op to non-integer"
  | Int _, _ ->
      failwith "Graphs.evaluator: integer cannot be applied"
  | State _, _ ->
      failwith "Graphs.evaluator: state cannot be applied"
  | Transform f, State x ->
      State (f x)
  | Transform _, _ ->
      failwith "Graphs.evaluator: apply of transform to non-state"
  | App1 f, Transform x ->
      Transform (f x)
  | App1 _, _ ->
      failwith "Graphs.evaluator: apply of app1 to non-transform"
  | App2 f, Transform x ->
      App1 (f x)
  | App2 _, _ ->
      failwith "Graphs.evaluator: apply of app2 to non-transform"
  | App3 f, Transform x ->
      App2 (f x)
  | App3 _, _ ->
      failwith "Graphs.evaluator: apply of app3 to non-transform"
  | For for_op, Int i ->
      App2 (for_op i)
  | For _, _ ->
      failwith "Graphs.evaluator: apply of for_i to non-integer"

let initial_primitives_types_alist ~max_node_color =
  ( List.range 0 @@ max 10 max_node_color
  |> List.map ~f:(fun i -> (string_of_int i, graph_int)) )
  @ [ ("plus", graph_int_binop)
    ; ("mult", graph_int_binop)
    ; ("identity", graph_transform)
    ; ("reorient", graph_app1)
    ; ("next", graph_app1)
    ; ("set_color_under_cursor", graph_app1)
    ; ("reset_color", graph_app1)
    ; ("reset_cursor", graph_app1)
    ; ("traverse", graph_app1)
    ; ("add", graph_app1)
    ; ("if_traversable", graph_app3)
    ; ("if_current", graph_app3)
    ; ("connect", graph_app1)
    ; ("push_pos", graph_app1)
    ; ("pop_pos", graph_app1)
    ; ("push_color", graph_app1)
    ; ("pop_color", graph_app1)
    ; ("for_i", graph_for)
    ; ("pos_proc", graph_app2)
    ; ("color_proc", graph_app2) ]

let initial_primitives_list ~max_node_color =
  initial_primitives_types_alist ~max_node_color
  |> List.map ~f:(fun (name, ty) -> Primitive {name; ty})

let initial_primitives ~max_node_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Primitive {name; ty}))
  @@ initial_primitives_types_alist ~max_node_color

let initial_dsl ~max_node_color =
  dsl_of_primitives graph_state @@ initial_primitives_list ~max_node_color

let initial_primitive_entries ~max_node_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map (initial_dsl ~max_node_color).library ~f:(fun ent ->
         (ent.name, ent) )

let rec reduce_identity identity_type = function
  | Abstraction b -> (
    match reduce_identity identity_type b with
    | Index 0 | Primitive {name= "identity"; _} ->
        Primitive {name= "identity"; ty= identity_type}
    | b' ->
        Abstraction b' )
  | Apply (f, x) -> (
    match reduce_identity identity_type f with
    | Primitive {name= "identity"; _} ->
        reduce_identity identity_type x
    | f' ->
        Apply (f', reduce_identity identity_type x) )
  | Invented (ty, _) when equal_dc_type ty identity_type ->
      Primitive {name= "identity"; ty= identity_type}
  | (Invented _ | Index _ | Primitive _) as p ->
      p

let naturalize (ty : dc_type) (f : graph_value executable -> graph_value option)
    : graph_value option =
  if equal_dc_type ty graph_transform then
    Some
      (Transform
         (fun s ->
           match f (Base (State s)) with
           | Some (State s') ->
               s'
           | _ ->
               failwith "could not naturalize graph transform" ) )
  else None

let evaluate_with_initial ~max_node_color =
  evaluate
    ~preprocess:(reduce_identity graph_transform)
    naturalize (lookup ~max_node_color) eval
    [Primitive {name= "initial"; ty= graph_state}]

let evaluate ~max_node_color ~timeout ~attempts p =
  Option.value_map ~default:None ~f:Fn.id
  @@ Util.run_for_interval ~attempts timeout (fun () ->
         try
           match evaluate_with_initial ~max_node_color p with
           | Some (State out) ->
               Some out
           | _ ->
               failwith
               @@ Format.sprintf
                    "evaluate: graph program did not output a state: %s"
                    (string_of_program p)
         with _ ->
           Format.eprintf "ERROR: %s\n" @@ string_of_program p ;
           None )
