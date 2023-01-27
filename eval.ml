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
  | Op "save" ->
      Exists (TStateOp Operations.save, RArrow (RState, RState))
  | Op "next_port" ->
      Exists
        ( TStateOpComp1 Operations.next_port
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "prev_port" ->
      Exists
        ( TStateOpComp1 Operations.prev_port
        , RArrow (RArrow (RState, RState), RArrow (RState, RState)) )
  | Op "port_func" ->
      Exists
        ( TStateOpComp2 Operations.port_func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "pos_func" ->
      Exists
        ( TStateOpComp2 Operations.pos_func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "func" ->
      Exists
        ( TStateOpComp2 Operations.func
        , RArrow
            ( RArrow (RState, RState)
            , RArrow (RArrow (RState, RState), RArrow (RState, RState)) ) )
  | Op "if_positions_equal" ->
      Exists
        ( TStateOpComp5 Operations.if_positions_equal
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
  | Op "move" ->
      Exists
        ( TStateOpComp1 Operations.move
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

let initial_primitives_types_alist =
  [ ("identity", graph_transform)
  ; ("next_port", graph_app1)
  ; ("prev_port", graph_app1)
  ; ("port_func", graph_app2)
  ; ("pos_func", graph_app2)
  ; ("func", graph_app2)
  ; ("if_positions_equal", graph_app5)
  ; ("move", graph_app1)
  ; ("add_nb", graph_app1)
  ; ("add_conn", graph_app3) ]

let all_primitives_types_alist =
  initial_primitives_types_alist
  @ [("initial", graph_state); ("save", graph_transform)]

let initial_primitives_list =
  List.map initial_primitives_types_alist ~f:(fun (name, ty) ->
      Program.Primitive {name; ty} )

let all_primitives_list =
  List.map all_primitives_types_alist ~f:(fun (name, ty) ->
      Program.Primitive {name; ty} )

let initial_primitives =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Program.Primitive {name; ty}))
  @@ initial_primitives_types_alist

let all_primitives =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Program.Primitive {name; ty}))
  @@ all_primitives_types_alist

let initial_dsl = Dsl.of_primitives graph_state @@ initial_primitives_list

let initial_primitive_entries =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun ent -> (Dsl_entry.stitch_name ent, ent))
  @@ Dsl.library initial_dsl

let rec var_of_int i =
  if i > 0 then VarSucc (var_of_int (i - 1))
  else if i = 0 then VarZero
  else failwith "indices must be greater than or equal to zero"

let rec expr_of_generic ~max_conn : Arg_typed_program.t -> expr = function
  | ATIndex i ->
      var_of_int i
  | ATPrimitive name -> (
    try
      let n = int_of_string name in
      EInt n
    with Failure _ ->
      if String.(name = "initial") then EState (State.empty ~max_conn)
      else Op name )
  | ATApply (f, x) ->
      Application (expr_of_generic ~max_conn f, expr_of_generic ~max_conn x)
  | ATAbstraction (ty, b) -> (
    match Reified_type.of_type ty with
    | AnyTy ty' ->
        Abstraction (ty', expr_of_generic ~max_conn b) )

let evaluate ~max_conn ~timeout ~attempts p g =
  Option.value_map ~default:None ~f:Fn.id
  @@ Util.run_for_interval ~attempts timeout (fun () ->
         try
           match typecheck_and_eval @@ expr_of_generic ~max_conn g with
           | ExistsValue _ ->
               Some ()
         with e ->
           Format.eprintf "ERROR: %s\n" @@ Program.to_string p ;
           raise e )
