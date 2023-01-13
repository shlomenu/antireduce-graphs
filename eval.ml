open Core
open Antireduce
open Type
open Program
open Dsl
open State

type _ ty =
  | Integer : int ty
  | State : state ty
  | TArrow : 'a ty * 'b ty -> ('a -> 'b) ty

type (_, _) eq = Refl : ('a, 'a) eq

let rec equal_ty : type a b. a ty -> b ty -> (a, b) eq option =
 fun ty_a ty_by ->
  match (ty_a, ty_by) with
  | Integer, Integer ->
      Some Refl
  | State, State ->
      Some Refl
  | TArrow (ty_a', ty_a''), TArrow (ty_b', ty_b'') -> (
    match (equal_ty ty_a' ty_b', equal_ty ty_a'' ty_b'') with
    | Some Refl, Some Refl ->
        Some Refl
    | _ ->
        None )
  | _ ->
      None

type _ context =
  | CEmpty : unit context
  | CBinding : 'a context * 't ty -> ('a * 't) context

type expr =
  | Int of int
  | State of state
  | Op of string
  | Application of expr * expr
  | Abstraction : 'a ty * expr -> expr
  | VarZero
  | VarSucc of expr

type (_, _) texpr =
  | TInt : int -> ('tc, int) texpr
  | TState : state -> ('tc, state) texpr
  | TIntOp2 : (int -> int -> int) -> ('tc, int -> int -> int) texpr
  | TStateOp : (state -> state) -> ('tc, state -> state) texpr
  | TStateOpComp1 :
      ((state -> state) -> state -> state)
      -> ('tc, (state -> state) -> state -> state) texpr
  | TStateOpComp2 :
      ((state -> state) -> (state -> state) -> state -> state)
      -> ('tc, (state -> state) -> (state -> state) -> state -> state) texpr
  | TStateOpComp3 :
      (   (state -> state)
       -> (state -> state)
       -> (state -> state)
       -> state
       -> state )
      -> ( 'tc
         ,    (state -> state)
           -> (state -> state)
           -> (state -> state)
           -> state
           -> state )
         texpr
  | TStateOpComp5 :
      (   (state -> state)
       -> (state -> state)
       -> (state -> state)
       -> (state -> state)
       -> (state -> state)
       -> state
       -> state )
      -> ( 'tc
         ,    (state -> state)
           -> (state -> state)
           -> (state -> state)
           -> (state -> state)
           -> (state -> state)
           -> state
           -> state )
         texpr
  | TFor :
      (int -> (state -> state) -> (state -> state) -> state -> state)
      -> ( 'tc
         , int -> (state -> state) -> (state -> state) -> state -> state )
         texpr
  | TApplication :
      ('tc, 't1 -> 't2) texpr * ('tc, 't1) texpr
      -> ('tc, 't2) texpr
  | TAbstraction : ('tc * 't1, 't2) texpr -> ('tc, 't1 -> 't2) texpr
  | TVarZero : ('tc * 't, 't) texpr
  | TVarSucc : ('tc, 't1) texpr -> ('tc * 't2, 't1) texpr

type _ exists_texpr = Exists : ('c, 't) texpr * 't ty -> 'c exists_texpr

let rec typecheck : type c. c context -> expr -> c exists_texpr =
 fun cxt e ->
  match e with
  | Int i ->
      Exists (TInt i, Integer)
  | State s ->
      Exists (TState s, State)
  | Op "plus" ->
      Exists (TIntOp2 ( + ), TArrow (Integer, TArrow (Integer, Integer)))
  | Op "mult" ->
      Exists (TIntOp2 ( * ), TArrow (Integer, TArrow (Integer, Integer)))
  | Op "reorient" ->
      Exists
        ( TStateOpComp1 reorient
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "next" ->
      Exists
        ( TStateOpComp1 next
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "set_color_under_cursor" ->
      Exists
        ( TStateOpComp1 set_color_under_cursor
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "reset_color" ->
      Exists
        ( TStateOpComp1 reset_color
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "reset_cursor" ->
      Exists
        ( TStateOpComp1 reset_cursor
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "traverse" ->
      Exists
        ( TStateOpComp1 traverse
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "add" ->
      Exists
        ( TStateOpComp1 add
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "if_traversable" ->
      Exists
        ( TStateOpComp3 if_traversable
        , TArrow
            ( TArrow (State, State)
            , TArrow
                ( TArrow (State, State)
                , TArrow (TArrow (State, State), TArrow (State, State)) ) ) )
  | Op "if_current" ->
      Exists
        ( TStateOpComp3 if_current
        , TArrow
            ( TArrow (State, State)
            , TArrow
                ( TArrow (State, State)
                , TArrow (TArrow (State, State), TArrow (State, State)) ) ) )
  | Op "connect" ->
      Exists
        ( TStateOpComp1 connect
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "push_pos" ->
      Exists
        ( TStateOpComp1 push_pos
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "pop_pos" ->
      Exists
        ( TStateOpComp1 pop_pos
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "push_color" ->
      Exists
        ( TStateOpComp1 push_color
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "pop_color" ->
      Exists
        ( TStateOpComp1 pop_color
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "for_i" ->
      Exists
        ( TFor for_i
        , TArrow
            ( Integer
            , TArrow
                ( TArrow (State, State)
                , TArrow (TArrow (State, State), TArrow (State, State)) ) ) )
  | Op "pos_proc" ->
      Exists
        ( TStateOpComp2 pos_proc
        , TArrow
            ( TArrow (State, State)
            , TArrow (TArrow (State, State), TArrow (State, State)) ) )
  | Op "color_proc" ->
      Exists
        ( TStateOpComp2 color_proc
        , TArrow
            ( TArrow (State, State)
            , TArrow (TArrow (State, State), TArrow (State, State)) ) )
  | Op "save" ->
      Exists (TStateOp save, TArrow (State, State))
  | Op "switch_direction" ->
      Exists
        ( TStateOpComp1 switch_direction
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "select_next" ->
      Exists
        ( TStateOpComp1 select_next
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "select_prev" ->
      Exists
        ( TStateOpComp1 select_prev
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "read_color" ->
      Exists
        ( TStateOpComp1 read_color
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "color_func" ->
      Exists
        ( TStateOpComp2 color_func
        , TArrow
            ( TArrow (State, State)
            , TArrow (TArrow (State, State), TArrow (State, State)) ) )
  | Op "loc_func" ->
      Exists
        ( TStateOpComp2 loc_func
        , TArrow
            ( TArrow (State, State)
            , TArrow (TArrow (State, State), TArrow (State, State)) ) )
  | Op "dir_func" ->
      Exists
        ( TStateOpComp2 dir_func
        , TArrow
            ( TArrow (State, State)
            , TArrow (TArrow (State, State), TArrow (State, State)) ) )
  | Op "func" ->
      Exists
        ( TStateOpComp2 func
        , TArrow
            ( TArrow (State, State)
            , TArrow (TArrow (State, State), TArrow (State, State)) ) )
  | Op "if_colors_equal" ->
      Exists
        ( TStateOpComp5 if_colors_equal
        , TArrow
            ( TArrow (State, State)
            , TArrow
                ( TArrow (State, State)
                , TArrow
                    ( TArrow (State, State)
                    , TArrow
                        ( TArrow (State, State)
                        , TArrow (TArrow (State, State), TArrow (State, State))
                        ) ) ) ) )
  | Op "if_locs_equal" ->
      Exists
        ( TStateOpComp5 if_locs_equal
        , TArrow
            ( TArrow (State, State)
            , TArrow
                ( TArrow (State, State)
                , TArrow
                    ( TArrow (State, State)
                    , TArrow
                        ( TArrow (State, State)
                        , TArrow (TArrow (State, State), TArrow (State, State))
                        ) ) ) ) )
  | Op "move_selected" ->
      Exists
        ( TStateOpComp1 move_selected
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "add_nb" ->
      Exists
        ( TStateOpComp1 add_nb
        , TArrow (TArrow (State, State), TArrow (State, State)) )
  | Op "add_conn" ->
      Exists
        ( TStateOpComp3 add_conn
        , TArrow
            ( TArrow (State, State)
            , TArrow
                ( TArrow (State, State)
                , TArrow (TArrow (State, State), TArrow (State, State)) ) ) )
  | Op unknown_name ->
      failwith @@ Format.sprintf "unrecognized primitive: %s" unknown_name
  | Abstraction (parameter_ty, b) -> (
    match typecheck (CBinding (cxt, parameter_ty)) b with
    | Exists (b', terminal_ty) ->
        Exists (TAbstraction b', TArrow (parameter_ty, terminal_ty)) )
  | Application (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (f', f_ty), Exists (x', x_ty) -> (
      match f_ty with
      | TArrow (x_ty', terminal_ty) -> (
        match equal_ty x_ty x_ty' with
        | Some Refl ->
            Exists (TApplication (f', x'), terminal_ty)
        | None ->
            failwith "" )
      | _ ->
          failwith "" ) )
  | VarZero -> (
    match cxt with
    | CEmpty ->
        failwith ""
    | CBinding (_, ty) ->
        Exists (TVarZero, ty) )
  | VarSucc e -> (
    match cxt with
    | CEmpty ->
        failwith ""
    | CBinding (cxt', _) -> (
      match typecheck cxt' e with
      | Exists (te, e_ty) ->
          Exists (TVarSucc te, e_ty) ) )

let rec eval : type c t. c -> (c, t) texpr -> t =
 fun env e ->
  match e with
  | TInt i ->
      i
  | TState s ->
      s
  | TIntOp2 f ->
      f
  | TStateOp f ->
      f
  | TStateOpComp1 f ->
      f
  | TStateOpComp2 f ->
      f
  | TStateOpComp3 f ->
      f
  | TStateOpComp5 f ->
      f
  | TFor f ->
      f
  | TVarZero ->
      let _, x = env in
      x
  | TVarSucc e ->
      let env, _ = env in
      eval env e
  | TAbstraction e ->
      fun x -> eval (env, x) e
  | TApplication (f, x) ->
      (eval env f) (eval env x)

type exists_value = ExistsValue : 't -> exists_value

let typecheck_and_eval e =
  match typecheck CEmpty e with Exists (te, _) -> ExistsValue (eval () te)

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

let graph_app5 =
  graph_transform @> graph_transform @> graph_transform @> graph_transform
  @> graph_transform @> graph_state @> graph_state

let graph_for =
  graph_int @> graph_transform @> graph_transform @> graph_state @> graph_state

let initial_nonintegral_v1_primitives_types_alist =
  [ ("plus", graph_int_binop)
  ; ("mult", graph_int_binop)
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

let all_nonintegral_v1_primitives_types_alist =
  initial_nonintegral_v1_primitives_types_alist
  @ [("initial", graph_state); ("save", graph_transform)]

let initial_v1_primitives_types_alist ~max_color =
  ( List.range ~stop:`inclusive 0 @@ max 10 max_color
  |> List.map ~f:(fun i -> (string_of_int i, graph_int)) )
  @ initial_nonintegral_v1_primitives_types_alist

let initial_v2_primitives_types_alist =
  [ ("identity", graph_transform)
  ; ("switch_direction", graph_app1)
  ; ("select_next", graph_app1)
  ; ("select_prev", graph_app1)
  ; ("read_color", graph_app1)
  ; ("color_func", graph_app2)
  ; ("loc_func", graph_app2)
  ; ("dir_func", graph_app2)
  ; ("func", graph_app2)
  ; ("if_colors_equal", graph_app5)
  ; ("if_locs_equal", graph_app5)
  ; ("move_selected", graph_app1)
  ; ("add_nb", graph_app1)
  ; ("add_conn", graph_app3) ]

let initial_primitives_types_alist ~max_color:_ =
  initial_v2_primitives_types_alist

let all_v1_primitives_types_alist ~max_color =
  ( List.range ~stop:`inclusive 0 @@ max 10 max_color
  |> List.map ~f:(fun i -> (string_of_int i, graph_int)) )
  @ all_nonintegral_v1_primitives_types_alist

let all_v2_primitives_types_alist =
  initial_v2_primitives_types_alist
  @ [("initial", graph_state); ("save", graph_transform)]

let all_primitives_types_alist ~max_color:_ = all_v2_primitives_types_alist

let initial_primitives_list ~max_color =
  initial_primitives_types_alist ~max_color
  |> List.map ~f:(fun (name, ty) -> Primitive {name; ty})

let all_primitives_list ~max_color =
  all_primitives_types_alist ~max_color
  |> List.map ~f:(fun (name, ty) -> Primitive {name; ty})

let initial_primitives ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Primitive {name; ty}))
  @@ initial_primitives_types_alist ~max_color

let all_primitives ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Primitive {name; ty}))
  @@ all_primitives_types_alist ~max_color

let initial_dsl ~max_color =
  dsl_of_primitives graph_state @@ initial_primitives_list ~max_color

let initial_primitive_entries ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map (initial_dsl ~max_color).library ~f:(fun ent -> (ent.name, ent))

let rec var_of_int i =
  if i > 0 then VarSucc (var_of_int (i - 1))
  else if i = 0 then VarZero
  else failwith "indices must be greater than or equal to zero"

type any_ty = AnyTy : 'a ty -> any_ty

let rec ty_of_dc_type : dc_type -> any_ty = function
  | Arrow {left; right; _} -> (
    match (ty_of_dc_type left, ty_of_dc_type right) with
    | AnyTy t_1, AnyTy t_2 ->
        AnyTy (TArrow (t_1, t_2)) )
  | Id _ ->
      failwith "type variable in unified generic expression"
  | Constructor {name; parameters; _} -> (
      if not (List.is_empty parameters) then
        failwith "graph domain has only zero arity constructors"
      else
        match name with
        | "int" ->
            AnyTy Integer
        | "graph_state" ->
            AnyTy State
        | _ ->
            failwith "unrecognized constructor" )

let rec expr_of_generic ~max_color = function
  | GIndex i ->
      var_of_int i
  | GPrimitive name -> (
    try
      let n = int_of_string name in
      Int n
    with Failure _ ->
      if String.(name = "initial") then State (initial_state ~max_color)
      else Op name )
  | GApply (f, x) ->
      Application (expr_of_generic ~max_color f, expr_of_generic ~max_color x)
  | GAbstraction (ty, b) -> (
    match ty_of_dc_type ty with
    | AnyTy ty' ->
        Abstraction (ty', expr_of_generic ~max_color b) )

let evaluate ~max_color ~timeout ~attempts p g =
  Option.value_map ~default:None ~f:Fn.id
  @@ Util.run_for_interval ~attempts timeout (fun () ->
         try
           match typecheck_and_eval @@ expr_of_generic ~max_color g with
           | ExistsValue _ ->
               Some ()
         with e ->
           Format.eprintf "ERROR: %s\n" @@ string_of_program p ;
           raise e )
