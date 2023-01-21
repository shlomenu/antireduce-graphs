open Core
open Antireduce

module Reified_type = struct
  type _ t =
    | RInt : int t
    | RState : State.t t
    | RArrow : 'a t * 'b t -> ('a -> 'b) t

  type (_, _) eq = Refl : ('a, 'a) eq

  let rec equal : type a b. a t -> b t -> (a, b) eq option =
   fun ty_a ty_by ->
    match (ty_a, ty_by) with
    | RInt, RInt ->
        Some Refl
    | RState, RState ->
        Some Refl
    | RArrow (ty_a', ty_a''), RArrow (ty_b', ty_b'') -> (
      match (equal ty_a' ty_b', equal ty_a'' ty_b'') with
      | Some Refl, Some Refl ->
          Some Refl
      | _ ->
          None )
    | _ ->
        None

  type any_ty = AnyTy : 'a t -> any_ty

  let rec of_type : Type.t -> any_ty = function
    | Arrow {left; right; _} -> (
      match (of_type left, of_type right) with
      | AnyTy t_1, AnyTy t_2 ->
          AnyTy (RArrow (t_1, t_2)) )
    | Id _ ->
        failwith "type variable in unified generic expression"
    | Constructor {name; parameters; _} -> (
        if not (List.is_empty parameters) then
          failwith "graph domain has only zero arity constructors"
        else
          match name with
          | "int" ->
              AnyTy RInt
          | "graph_state" ->
              AnyTy RState
          | _ ->
              failwith "unrecognized constructor" )
end

type _ context =
  | CEmpty : unit context
  | CBinding : 'a context * 't Reified_type.t -> ('a * 't) context

type expr =
  | EInt of int
  | EState of State.t
  | Op of string
  | Application of expr * expr
  | Abstraction : 'a Reified_type.t * expr -> expr
  | VarZero
  | VarSucc of expr

type (_, _) texpr =
  | TInt : int -> ('tc, int) texpr
  | TState : State.t -> ('tc, State.t) texpr
  | TIntOp2 : (int -> int -> int) -> ('tc, int -> int -> int) texpr
  | TStateOp : (State.t -> State.t) -> ('tc, State.t -> State.t) texpr
  | TStateOpComp1 :
      ((State.t -> State.t) -> State.t -> State.t)
      -> ('tc, (State.t -> State.t) -> State.t -> State.t) texpr
  | TStateOpComp2 :
      ((State.t -> State.t) -> (State.t -> State.t) -> State.t -> State.t)
      -> ( 'tc
         , (State.t -> State.t) -> (State.t -> State.t) -> State.t -> State.t
         )
         texpr
  | TStateOpComp3 :
      (   (State.t -> State.t)
       -> (State.t -> State.t)
       -> (State.t -> State.t)
       -> State.t
       -> State.t )
      -> ( 'tc
         ,    (State.t -> State.t)
           -> (State.t -> State.t)
           -> (State.t -> State.t)
           -> State.t
           -> State.t )
         texpr
  | TStateOpComp5 :
      (   (State.t -> State.t)
       -> (State.t -> State.t)
       -> (State.t -> State.t)
       -> (State.t -> State.t)
       -> (State.t -> State.t)
       -> State.t
       -> State.t )
      -> ( 'tc
         ,    (State.t -> State.t)
           -> (State.t -> State.t)
           -> (State.t -> State.t)
           -> (State.t -> State.t)
           -> (State.t -> State.t)
           -> State.t
           -> State.t )
         texpr
  | TFor :
      (int -> (State.t -> State.t) -> (State.t -> State.t) -> State.t -> State.t)
      -> ( 'tc
         ,    int
           -> (State.t -> State.t)
           -> (State.t -> State.t)
           -> State.t
           -> State.t )
         texpr
  | TApplication :
      ('tc, 't1 -> 't2) texpr * ('tc, 't1) texpr
      -> ('tc, 't2) texpr
  | TAbstraction : ('tc * 't1, 't2) texpr -> ('tc, 't1 -> 't2) texpr
  | TVarZero : ('tc * 't, 't) texpr
  | TVarSucc : ('tc, 't1) texpr -> ('tc * 't2, 't1) texpr

type _ exists_texpr =
  | Exists : ('c, 't) texpr * 't Reified_type.t -> 'c exists_texpr

let rec typecheck : type c. c context -> expr -> c exists_texpr =
 fun cxt e ->
  match e with
  | EInt i ->
      Exists (TInt i, RInt)
  | EState s ->
      Exists (TState s, RState)
  | Op "plus" ->
      Exists (TIntOp2 ( + ), RArrow (RInt, RArrow (RInt, RInt)))
  | Op "mult" ->
      Exists (TIntOp2 ( * ), RArrow (RInt, RArrow (RInt, RInt)))
  | Op "reorient" ->
      Exists
        ( TStateOpComp1 Operations.reorient
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "next" ->
      Exists
        ( TStateOpComp1 Operations.next
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "set_color_under_cursor" ->
      Exists
        ( TStateOpComp1 Operations.set_color_under_cursor
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "reset_color" ->
      Exists
        ( TStateOpComp1 Operations.reset_color
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "reset_cursor" ->
      Exists
        ( TStateOpComp1 Operations.reset_cursor
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "traverse" ->
      Exists
        ( TStateOpComp1 Operations.traverse
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "add" ->
      Exists
        ( TStateOpComp1 Operations.add
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "if_traversable" ->
      Exists
        ( TStateOpComp3 Operations.if_traversable
        , RArrow
            ( RArrow (RState, RState)
            , RArrow
                ( RArrow (RState, RState)
                , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
        )
  | Op "if_current" ->
      Exists
        ( TStateOpComp3 Operations.if_current
        , RArrow
            ( RArrow (RState, RState)
            , RArrow
                ( RArrow (RState, RState)
                , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
        )
  | Op "connect" ->
      Exists
        ( TStateOpComp1 Operations.connect
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "push_pos" ->
      Exists
        ( TStateOpComp1 Operations.push_pos
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "pop_pos" ->
      Exists
        ( TStateOpComp1 Operations.pop_pos
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "push_color" ->
      Exists
        ( TStateOpComp1 Operations.push_color
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "pop_color" ->
      Exists
        ( TStateOpComp1 Operations.pop_color
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "for_i" ->
      Exists
        ( TFor Operations.for_i
        , RArrow
            ( RInt
            , RArrow
                ( RArrow (RState, RState)
                , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
        )
  | Op "pos_proc" ->
      Exists
        ( TStateOpComp2 Operations.pos_proc
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "color_proc" ->
      Exists
        ( TStateOpComp2 Operations.color_proc
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "save" ->
      Exists (TStateOp Operations.save, RArrow (RState, RState))
  | Op "switch_direction" ->
      Exists
        ( TStateOpComp1 Operations.switch_direction
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "select_next" ->
      Exists
        ( TStateOpComp1 Operations.select_next
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "select_prev" ->
      Exists
        ( TStateOpComp1 Operations.select_prev
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "read_color" ->
      Exists
        ( TStateOpComp1 Operations.read_color
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "color_func" ->
      Exists
        ( TStateOpComp2 Operations.color_func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "loc_func" ->
      Exists
        ( TStateOpComp2 Operations.loc_func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "dir_func" ->
      Exists
        ( TStateOpComp2 Operations.dir_func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "func" ->
      Exists
        ( TStateOpComp2 Operations.func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "if_colors_equal" ->
      Exists
        ( TStateOpComp5 Operations.if_colors_equal
        , RArrow
            ( RArrow (RState, RState)
            , RArrow
                ( RArrow (RState, RState)
                , RArrow
                    ( RArrow (RState, RState)
                    , RArrow
                        ( RArrow (RState, RState)
                        , RArrow
                            (RArrow (RState, RState), RArrow (RState, RState))
                        ) ) ) ) )
  | Op "if_locs_equal" ->
      Exists
        ( TStateOpComp5 Operations.if_locs_equal
        , RArrow
            ( RArrow (RState, RState)
            , RArrow
                ( RArrow (RState, RState)
                , RArrow
                    ( RArrow (RState, RState)
                    , RArrow
                        ( RArrow (RState, RState)
                        , RArrow
                            (RArrow (RState, RState), RArrow (RState, RState))
                        ) ) ) ) )
  | Op "move_selected" ->
      Exists
        ( TStateOpComp1 Operations.move_selected
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "add_nb" ->
      Exists
        ( TStateOpComp1 Operations.add_nb
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "add_conn" ->
      Exists
        ( TStateOpComp3 Operations.add_conn
        , RArrow
            ( RArrow (RState, RState)
            , RArrow
                ( RArrow (RState, RState)
                , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
        )
  | Op "identity" ->
      Exists (TStateOp Operations.identity, RArrow (RState, RState))
  | Op unknown_name ->
      failwith @@ Format.sprintf "unrecognized primitive: %s" unknown_name
  | Abstraction (parameter_ty, b) -> (
    match typecheck (CBinding (cxt, parameter_ty)) b with
    | Exists (b', terminal_ty) ->
        Exists (TAbstraction b', RArrow (parameter_ty, terminal_ty)) )
  | Application (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (f', f_ty), Exists (x', x_ty) -> (
      match f_ty with
      | RArrow (x_ty', terminal_ty) -> (
        match Reified_type.equal x_ty x_ty' with
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

let graph_int = Type.kind "int" []

let graph_int_binop = Type.(graph_int @> graph_int @> graph_int)

let graph_state = Type.kind "graph_state" []

let graph_transform = Type.(graph_state @> graph_state)

let graph_app1 = Type.(graph_transform @> graph_state @> graph_state)

let graph_app2 =
  Type.(graph_transform @> graph_transform @> graph_state @> graph_state)

let graph_app3 =
  Type.(
    graph_transform @> graph_transform @> graph_transform @> graph_state
    @> graph_state )

let graph_app5 =
  Type.(
    graph_transform @> graph_transform @> graph_transform @> graph_transform
    @> graph_transform @> graph_state @> graph_state )

let graph_for =
  Type.(
    graph_int @> graph_transform @> graph_transform @> graph_state
    @> graph_state )

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
  |> List.map ~f:(fun (name, ty) -> Program.Primitive {name; ty})

let all_primitives_list ~max_color =
  all_primitives_types_alist ~max_color
  |> List.map ~f:(fun (name, ty) -> Program.Primitive {name; ty})

let initial_primitives ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Program.Primitive {name; ty}))
  @@ initial_primitives_types_alist ~max_color

let all_primitives ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Program.Primitive {name; ty}))
  @@ all_primitives_types_alist ~max_color

let initial_dsl ~max_color =
  Dsl.of_primitives graph_state @@ initial_primitives_list ~max_color

let initial_primitive_entries ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map (initial_dsl ~max_color).library ~f:(fun ent ->
         (ent.dc_name, ent) )

let rec var_of_int i =
  if i > 0 then VarSucc (var_of_int (i - 1))
  else if i = 0 then VarZero
  else failwith "indices must be greater than or equal to zero"

let rec expr_of_generic ~max_color : Arg_typed_program.t -> expr = function
  | ATIndex i ->
      var_of_int i
  | ATPrimitive name -> (
    try
      let n = int_of_string name in
      EInt n
    with Failure _ ->
      if String.(name = "initial") then EState (State.empty ~max_color)
      else Op name )
  | ATApply (f, x) ->
      Application (expr_of_generic ~max_color f, expr_of_generic ~max_color x)
  | ATAbstraction (ty, b) -> (
    match Reified_type.of_type ty with
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
           Format.eprintf "ERROR: %s\n" @@ Program.to_string p ;
           raise e )
