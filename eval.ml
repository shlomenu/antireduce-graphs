open Core
open Antireduce
open Type
open Program
open Dsl
open State

type _ ty =
  | Integer : int ty
  | State : state ty
  | Arrow : 'a ty * 'b ty -> ('a -> 'b) ty

type (_, _) texpr =
  | TInt : int -> ('c, int) texpr
  | TState : state -> ('c, state) texpr
  | TIntOp1 : ('c, int -> int) texpr * ('c, int) texpr -> ('c, int) texpr
  | TIntOp2 :
      ('c, int -> int -> int) texpr * ('c, int) texpr
      -> ('c, int -> int) texpr
  | TStateOp :
      ('c, state -> state) texpr * ('c, state) texpr
      -> ('c, state) texpr
  | TStateOpComp1 :
      ('c, (state -> state) -> state -> state) texpr
      * ('c, state -> state) texpr
      -> ('c, state -> state) texpr
  | TStateOpComp2 :
      ('c, (state -> state) -> (state -> state) -> state -> state) texpr
      * ('c, state -> state) texpr
      -> ('c, (state -> state) -> state -> state) texpr
  | TStateOpComp3 :
      ( 'c
      ,    (state -> state)
        -> (state -> state)
        -> (state -> state)
        -> state
        -> state )
      texpr
      * ('c, state -> state) texpr
      -> ('c, (state -> state) -> (state -> state) -> state -> state) texpr
  | TFor :
      ('c, int -> (state -> state) -> (state -> state) -> state -> state) texpr
      * ('c, int) texpr
      -> ('c, (state -> state) -> (state -> state) -> state -> state) texpr
  | TApplication : ('c, 't1 -> 't2) texpr * ('c, 't1) texpr -> ('c, 't2) texpr
  | TAbstraction : ('c * 't1, 't2) texpr -> ('c, 't1 -> 't2) texpr
  | TVarZero : ('c * 't, 't) texpr
  | TVarSucc : ('c, 't1) texpr -> ('c * 't2, 't1) texpr

type (_, _) eq = Refl : ('a, 'a) eq

let rec equal_ty : type a b. a ty -> b ty -> (a, b) eq option =
 fun ty_a ty_b ->
  match (ty_a, ty_b) with
  | Integer, Integer ->
      Some Refl
  | State, State ->
      Some Refl
  | Arrow (parameter_ty, terminal_ty), Arrow (parameter_ty', terminal_ty') -> (
    match
      (equal_ty parameter_ty parameter_ty', equal_ty terminal_ty terminal_ty')
    with
    | Some Refl, Some Refl ->
        Some Refl
    | _ ->
        None )
  | _ ->
      None

type _ is_int = IsInt : int is_int

let is_integer : type a. a ty -> a is_int option = function
  | Integer ->
      Some IsInt
  | _ ->
      None

type _ is_state = IsState : state is_state

let is_state : type a. a ty -> a is_state option = function
  | State ->
      Some IsState
  | _ ->
      None

type _ is_intop1 = IsIntOp1 : (int -> int) is_intop1

let is_intop1 : type a. a ty -> a is_intop1 option = function
  | Arrow (Integer, Integer) ->
      Some IsIntOp1
  | _ ->
      None

type _ is_intop2 = IsIntOp2 : (int -> int -> int) is_intop2

let is_intop2 : type a. a ty -> a is_intop2 option = function
  | Arrow (Integer, Arrow (Integer, Integer)) ->
      Some IsIntOp2
  | _ ->
      None

type _ is_stateop = IsStateOp : (state -> state) is_stateop

let is_stateop : type a. a ty -> a is_stateop option = function
  | Arrow (State, State) ->
      Some IsStateOp
  | _ ->
      None

type _ is_stateopcomp1 =
  | IsStateOpComp1 : ((state -> state) -> state -> state) is_stateopcomp1

let is_stateopcomp1 : type a. a ty -> a is_stateopcomp1 option = function
  | Arrow (Arrow (State, State), Arrow (State, State)) ->
      Some IsStateOpComp1
  | _ ->
      None

type _ is_stateopcomp2 =
  | IsStateOpComp2
      : ((state -> state) -> (state -> state) -> state -> state) is_stateopcomp2

let is_stateopcomp2 : type a. a ty -> a is_stateopcomp2 option = function
  | Arrow
      (Arrow (State, State), Arrow (Arrow (State, State), Arrow (State, State)))
    ->
      Some IsStateOpComp2
  | _ ->
      None

type _ is_stateopcomp3 =
  | IsStateOpComp3
      : (   (state -> state)
         -> (state -> state)
         -> (state -> state)
         -> state
         -> state )
        is_stateopcomp3

let is_stateopcomp3 : type a. a ty -> a is_stateopcomp3 option = function
  | Arrow
      ( Arrow (State, State)
      , Arrow
          ( Arrow (State, State)
          , Arrow (Arrow (State, State), Arrow (State, State)) ) ) ->
      Some IsStateOpComp3
  | _ ->
      None

type _ is_for =
  | IsFor
      : (int -> (state -> state) -> (state -> state) -> state -> state) is_for

let is_for : type a. a ty -> a is_for option = function
  | Arrow
      ( Integer
      , Arrow
          ( Arrow (State, State)
          , Arrow (Arrow (State, State), Arrow (State, State)) ) ) ->
      Some IsFor
  | _ ->
      None

type _ context =
  | CEmpty : unit context
  | CBinding : 'a context * 't ty -> ('a * 't) context

type expr =
  | Int of int
  | State of state
  | IntOp1 of expr * expr
  | IntOp2 of expr * expr
  | StateOp of expr * expr
  | StateOpComp1 of expr * expr
  | StateOpComp2 of expr * expr
  | StateOpComp3 of expr * expr
  | For of expr * expr
  | Application of expr * expr
  | Abstraction : 'a ty * expr -> expr
  | VarZero
  | VarSucc of expr

type _ exists_texpr = Exists : ('c, 't) texpr * 't ty -> 'c exists_texpr

let rec typecheck : type c. c context -> expr -> c exists_texpr =
 fun cxt e ->
  match e with
  | Int i ->
      Exists (TInt i, Integer)
  | State s ->
      Exists (TState s, State)
  | IntOp1 (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_intop1 f_ty, is_integer x_ty) with
      | Some IsIntOp1, Some IsInt ->
          Exists (TIntOp1 (tf, tx), x_ty)
      | _ ->
          failwith "" ) )
  | IntOp2 (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_intop2 f_ty, is_integer x_ty) with
      | Some IsIntOp2, Some IsInt ->
          Exists (TIntOp2 (tf, tx), Arrow (Integer, Integer))
      | _ ->
          failwith "" ) )
  | StateOp (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_stateop f_ty, is_state x_ty) with
      | Some IsStateOp, Some IsState ->
          Exists (TStateOp (tf, tx), x_ty)
      | _ ->
          failwith "" ) )
  | StateOpComp1 (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_stateopcomp1 f_ty, is_stateop x_ty) with
      | Some IsStateOpComp1, Some IsStateOp ->
          Exists (TStateOpComp1 (tf, tx), Arrow (State, State))
      | _ ->
          failwith "" ) )
  | StateOpComp2 (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_stateopcomp2 f_ty, is_stateop x_ty) with
      | Some IsStateOpComp2, Some IsStateOp ->
          Exists
            ( TStateOpComp2 (tf, tx)
            , Arrow (Arrow (State, State), Arrow (State, State)) )
      | _ ->
          failwith "" ) )
  | StateOpComp3 (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_stateopcomp3 f_ty, is_stateop x_ty) with
      | Some IsStateOpComp3, Some IsStateOp ->
          Exists
            ( TStateOpComp3 (tf, tx)
            , Arrow
                ( Arrow (State, State)
                , Arrow (Arrow (State, State), Arrow (State, State)) ) )
      | _ ->
          failwith "" ) )
  | For (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match (is_for f_ty, is_integer x_ty) with
      | Some IsFor, Some IsInt ->
          Exists
            ( TFor (tf, tx)
            , Arrow
                ( Arrow (State, State)
                , Arrow (Arrow (State, State), Arrow (State, State)) ) )
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
  | Abstraction (parameter_ty, e) -> (
    match typecheck (CBinding (cxt, parameter_ty)) e with
    | Exists (te, terminal_ty) ->
        Exists (TAbstraction te, Arrow (parameter_ty, terminal_ty)) )
  | Application (f, x) -> (
    match (typecheck cxt f, typecheck cxt x) with
    | Exists (tf, f_ty), Exists (tx, x_ty) -> (
      match f_ty with
      | Arrow (x_ty', terminal_ty) -> (
        match equal_ty x_ty x_ty' with
        | Some Refl ->
            Exists (TApplication (tf, tx), terminal_ty)
        | None ->
            failwith "" )
      | _ ->
          failwith "" ) )

let rec eval : type c t. c -> (c, t) texpr -> t =
 fun env e ->
  match e with
  | TInt i ->
      i
  | TState s ->
      s
  | TIntOp1 (f, x) ->
      (eval env f) (eval env x)
  | TIntOp2 (f, x) ->
      (eval env f) (eval env x)
  | TStateOp (f, x) ->
      (eval env f) (eval env x)
  | TStateOpComp1 (f, x) ->
      (eval env f) (eval env x)
  | TStateOpComp2 (f, x) ->
      (eval env f) (eval env x)
  | TStateOpComp3 (f, x) ->
      (eval env f) (eval env x)
  | TFor (f, x) ->
      (eval env f) (eval env x)
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
(*
   type _ typed_syntax =
     | TyInt : int typed_syntax
     | TyIntOp1 : (int -> int) typed_syntax
     | TyIntOp2 : (int -> int -> int) typed_syntax
     | TyState : state typed_syntax
     | TyTransform : (state -> state) typed_syntax
     | TyCompose1 : ((state -> state) -> state -> state) typed_syntax
     | TyCompose2
         : ((state -> state) -> (state -> state) -> state -> state) typed_syntax
     | TyCompose3
         : (   (state -> state)
            -> (state -> state)
            -> (state -> state)
            -> state
            -> state )
           typed_syntax
     | TyFor
         : (int -> (state -> state) -> (state -> state) -> state -> state)
           typed_syntax
     | TyApplication : ('a -> 'b) typed_syntax * 'a typed_syntax -> 'b typed_syntax
     | TyAbstraction : 'a typed_syntax * 'b typed_syntax -> ('a -> 'b) typed_syntax

   and _ graph_term =
     | Int : int -> int graph_term
     | IntOp1 : (int -> int) -> (int -> int) graph_term
     | IntOp2 : (int -> int -> int) -> (int -> int -> int) graph_term
     | State : state -> state graph_term
     | Transform : (state -> state) -> (state -> state) graph_term
     | App1 :
         ((state -> state) -> state -> state)
         -> ((state -> state) -> state -> state) graph_term
     | App2 :
         ((state -> state) -> (state -> state) -> state -> state)
         -> ((state -> state) -> (state -> state) -> state -> state) graph_term
     | App3 :
         (   (state -> state)
          -> (state -> state)
          -> (state -> state)
          -> state
          -> state )
         -> (   (state -> state)
             -> (state -> state)
             -> (state -> state)
             -> state
             -> state )
            graph_term
     | For :
         (int -> (state -> state) -> (state -> state) -> state -> state)
         -> (int -> (state -> state) -> (state -> state) -> state -> state)
            graph_term
     | Application : ('a -> 'b) graph_term * 'a graph_term -> 'b graph_term
     | Abstraction : 'a typed_syntax * 'b graph_term -> ('a -> 'b) graph_term

   type ('a, 'b) eq = Refl : ('a, 'a) eq

   let rec equal_typed_syntax ty_a ty_b =
     Option.is_some @@ typed_syntax_equality_proof_sym ty_a ty_b

   and typed_syntax_equality_proof_sym :
       type a b. a typed_syntax -> b typed_syntax -> (a, b) eq option =
    fun ty_a ty_b ->
     match (ty_a, ty_b) with
     | TyInt, TyInt ->
         Some Refl
     | TyIntOp1, TyIntOp1 ->
         Some Refl
     | TyIntOp2, TyIntOp2 ->
         Some Refl
     | TyState, TyState ->
         Some Refl
     | TyTransform, TyTransform ->
         Some Refl
     | TyCompose1, TyCompose1 ->
         Some Refl
     | TyCompose2, TyCompose2 ->
         Some Refl
     | TyCompose3, TyCompose3 ->
         Some Refl
     | TyFor, TyFor ->
         Some Refl
     | ( TyAbstraction (parameter_type, terminal_type)
       , TyAbstraction (parameter_type', terminal_type') ) -> (
       match
         ( typed_syntax_equality_proof_sym parameter_type parameter_type'
         , typed_syntax_equality_proof_sym terminal_type terminal_type' )
       with
       | Some Refl, Some Refl ->
           Some Refl
       | _ ->
           None )
     | ( TyApplication (function_type, parameter_type)
       , TyApplication (function_type', parameter_type') ) -> (
       match
         ( typed_syntax_equality_proof_sym function_type function_type'
         , typed_syntax_equality_proof_sym parameter_type parameter_type' )
       with
       | Some Refl, Some Refl ->
           Some Refl
       | _ ->
           None )
     | _ -> (
       match
         ( typed_syntax_equality_proof_assym ty_a ty_b
         , typed_syntax_equality_proof_assym ty_b ty_a )
       with
       | Some Refl, _ ->
           Some Refl
       | _, Some Refl ->
           Some Refl
       | _ ->
           None )

   and typed_syntax_equality_proof_assym :
       type a b. a typed_syntax -> b typed_syntax -> (a, b) eq option =
    fun ty_a ty_b ->
     match (ty_a, ty_b) with
     | TyApplication (TyIntOp1, TyInt), TyInt ->
         Some Refl
     | TyApplication (TyIntOp2, TyInt), TyIntOp1 ->
         Some Refl
     | TyApplication (TyTransform, TyState), TyState ->
         Some Refl
     | TyApplication (TyCompose1, TyTransform), TyTransform ->
         Some Refl
     | TyApplication (TyCompose2, TyTransform), TyCompose1 ->
         Some Refl
     | TyApplication (TyCompose3, TyTransform), TyCompose2 ->
         Some Refl
     | TyApplication (TyFor, TyInt), TyCompose2 ->
         Some Refl
     | ( TyApplication
           (TyAbstraction (parameter_type, terminal_type'), parameter_type')
       , terminal_type ) -> (
       match
         ( typed_syntax_equality_proof_sym parameter_type parameter_type'
         , typed_syntax_equality_proof_sym terminal_type terminal_type' )
       with
       | Some Refl, Some Refl ->
           Some Refl
       | _ ->
           None )
     | _ ->
         None

   type any_typed_syntax = Any : 'a typed_syntax -> any_typed_syntax

   type any_graph_term = AnyTerm : 'a graph_term -> any_graph_term

   let rec construct_type (req : any_typed_syntax option)
       (env : any_typed_syntax option list) : program -> any_typed_syntax option =
     let agreement requested inferred =
       match (requested, inferred) with
       | Some (Any program_type), Some (Any program_type') ->
           if equal_typed_syntax program_type program_type' then inferred else None
       | None, Some _ ->
           inferred
       | _ ->
           None
     in
     function
     | Index i ->
         agreement req @@ Option.join @@ List.nth env i
     | Primitive {name; _} ->
         let inferred =
           match name with
           | "plus" ->
               Some (Any TyIntOp2)
           | "mult" ->
               Some (Any TyIntOp2)
           | "initial" ->
               Some (Any TyState)
           | "identity" ->
               Some (Any TyTransform)
           | "reorient" ->
               Some (Any TyCompose1)
           | "next" ->
               Some (Any TyCompose1)
           | "set_color_under_cursor" ->
               Some (Any TyCompose1)
           | "reset_color" ->
               Some (Any TyCompose1)
           | "reset_cursor" ->
               Some (Any TyCompose1)
           | "traverse" ->
               Some (Any TyCompose1)
           | "add" ->
               Some (Any TyCompose1)
           | "if_traversable" ->
               Some (Any TyCompose3)
           | "if_current" ->
               Some (Any TyCompose3)
           | "connect" ->
               Some (Any TyCompose1)
           | "push_pos" ->
               Some (Any TyCompose1)
           | "pop_pos" ->
               Some (Any TyCompose1)
           | "push_color" ->
               Some (Any TyCompose1)
           | "pop_color" ->
               Some (Any TyCompose1)
           | "for_i" ->
               Some (Any TyFor)
           | "pos_proc" ->
               Some (Any TyCompose2)
           | "color_proc" ->
               Some (Any TyCompose2)
           | _ ->
               failwith "unrecognized primitive"
         in
         agreement req inferred
     | Invented (_, b) ->
         construct_type req env b
     | Abstraction b -> (
         let open Option.Let_syntax in
         match%bind req with
         | Any (TyAbstraction (parameter_type, terminal_type)) -> (
             match%bind
               construct_type (Some (Any terminal_type))
                 (Some (Any parameter_type) :: env)
                 b
             with
             | Any term_type' ->
                 Some (Any (TyAbstraction (parameter_type, term_type'))) )
         | _ ->
             None )
     | Apply (f, x) -> (
         let open Option.Let_syntax in
         match%bind req with
         | Any terminal_type -> (
             let if_app_equal ty_f ty_x =
               let terminal_type' = TyApplication (ty_f, ty_x) in
               if equal_typed_syntax terminal_type terminal_type' then
                 Some (Any terminal_type')
               else None
             in
             match (construct_type None env f, construct_type None env x) with
             | Some (Any TyIntOp2), Some (Any TyInt) ->
                 if_app_equal TyIntOp2 TyInt
             | Some (Any TyIntOp1), Some (Any TyInt) ->
                 if_app_equal TyIntOp1 TyInt
             | Some (Any TyCompose3), Some (Any TyTransform) ->
                 if_app_equal TyCompose3 TyTransform
             | Some (Any TyCompose2), Some (Any TyTransform) ->
                 if_app_equal TyCompose2 TyTransform
             | Some (Any TyCompose1), Some (Any TyTransform) ->
                 if_app_equal TyCompose1 TyTransform
             | Some (Any TyTransform), Some (Any TyState) ->
                 if_app_equal TyTransform TyState
             | Some (Any TyFor), Some (Any TyInt) ->
                 if_app_equal TyFor TyInt
             | Some (Any (TyAbstraction (parameter_type, terminal_type'))), None ->
                 if equal_typed_syntax terminal_type terminal_type' then
                   match%bind construct_type (Some (Any parameter_type)) env x with
                   | Any parameter_type' ->
                       if equal_typed_syntax parameter_type parameter_type' then
                         Some
                           (Any
                              (TyApplication
                                 ( TyAbstraction (parameter_type', terminal_type')
                                 , parameter_type' ) ) )
                       else None
                 else None
             | None, Some (Any parameter_type) -> (
                 match%bind
                   construct_type
                     (Some (Any (TyAbstraction (parameter_type, terminal_type))))
                     env f
                 with
                 | Any (TyAbstraction (parameter_type', terminal_type') as abs) ->
                     if
                       equal_typed_syntax parameter_type parameter_type'
                       && equal_typed_syntax terminal_type terminal_type'
                     then Some (Any (TyApplication (abs, parameter_type')))
                     else None )
             | None, None ->
                 None
             | _ ->
                 None ) )

   let rec construct ~(max_color : int)
       (env : (Int.t, any_graph_type, Int.comparator_witness) Map.t) :
       program -> any_graph_term = function
     | Index i ->
         AnyTerm
           ( (match Map.find_exn env i with AnyType (TyVar (Some ty)) -> ty)
           , Var i )
     | Primitive {name; _} -> (
       match name with
       | "plus" ->
           AnyTerm (TyIntOp2, IntOp2 ( + ))
       | "mult" ->
           AnyTerm (TyIntOp2, IntOp2 ( * ))
       | "initial" ->
           AnyTerm (TyState, State (initial_state ~max_color))
       | "identity" ->
           AnyTerm (TyTransform, Transform identity)
       | "reorient" ->
           AnyTerm (TyApp1, App1 reorient)
       | "next" ->
           AnyTerm (TyApp1, App1 next)
       | "set_color_under_cursor" ->
           AnyTerm (TyApp1, App1 set_color_under_cursor)
       | "reset_color" ->
           AnyTerm (TyApp1, App1 reset_color)
       | "reset_cursor" ->
           AnyTerm (TyApp1, App1 reset_cursor)
       | "traverse" ->
           AnyTerm (TyApp1, App1 traverse)
       | "add" ->
           AnyTerm (TyApp1, App1 add)
       | "if_traversable" ->
           AnyTerm (TyApp3, App3 if_traversable)
       | "if_current" ->
           AnyTerm (TyApp3, App3 if_current)
       | "connect" ->
           AnyTerm (TyApp1, App1 connect)
       | "push_pos" ->
           AnyTerm (TyApp1, App1 push_pos)
       | "pop_pos" ->
           AnyTerm (TyApp1, App1 pop_pos)
       | "push_color" ->
           AnyTerm (TyApp1, App1 push_color)
       | "pop_color" ->
           AnyTerm (TyApp1, App1 pop_color)
       | "for_i" ->
           AnyTerm (TyFor, For for_i)
       | "pos_proc" ->
           AnyTerm (TyApp2, App2 pos_proc)
       | "color_proc" ->
           AnyTerm (TyApp2, App2 color_proc)
       | _ ->
           failwith "unknown primitive" )
     | Invented (_, b) ->
         construct ~max_color b
     | Apply (f, x) as p -> (
         let app_fail name =
           let ps = string_of_program p in
           failwith @@ Format.sprintf "improper application of %s: %s" name ps
         in
         match (construct ~max_color f, construct ~max_color x) with
         | AnyTerm (TyIntOp2, f), AnyTerm (TyInt, x)
         | AnyTerm (TyIntOp2, f), AnyTerm (TyVar, x) ->
             AnyTerm (TyApp (TyIntOp2, TyInt), Application (f, x))
         | AnyTerm (TyIntOp2, _), _ ->
             app_fail "intop2"
         | AnyTerm (TyIntOp1, f), AnyTerm (TyInt, x) ->
             AnyTerm (TyApp (TyIntOp1, TyInt), Application (f, x))
         | AnyTerm (TyState, _), _ ->
             app_fail "state"
         | AnyTerm (TyTransform, f), AnyTerm (TyState, x) ->
             AnyTerm (TyApp (TyTransform, TyState), Application (f, x))
         | AnyTerm (TyTransform, _), _ ->
             app_fail "transform"
         | AnyTerm (TyApp1, f), AnyTerm (TyTransform, x) ->
             AnyTerm (TyApp (TyApp1, TyTransform), Application (f, x))
         | AnyTerm (TyApp1, _), _ ->
             app_fail "app1"
         | AnyTerm (TyApp2, f), AnyTerm (TyTransform, x) ->
             AnyTerm (TyApp (TyApp2, TyTransform), Application (f, x))
         | AnyTerm (TyApp2, _), _ ->
             app_fail "app2"
         | AnyTerm (TyApp3, f), AnyTerm (TyTransform, x) ->
             AnyTerm (TyApp (TyApp3, TyTransform), Application (f, x))
         | AnyTerm (TyApp3, _), _ ->
             app_fail "app3"
         | AnyTerm (TyFor, f), AnyTerm (TyInt, x) ->
             AnyTerm (TyApp (TyFor, TyInt), Application (f, x))
         | AnyTerm (TyFor, _), _ ->
             app_fail "for" )
     | Abstraction b -> (
       match construct ~max_color b with
       | AnyTerm (body_type, body_term) ->
           AnyTerm (TyAbs (TyVar, body_type), Abstraction (TyVar, body_term)) ) *)

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

(* let graph_values ~max_color =
     Hashtbl.of_alist_exn (module String)
     @@ ( List.range 0 @@ max 11 max_color
        |> List.map ~f:(fun i -> (string_of_int i, Int i)) )
     @ [ ("plus", IntOp2 ( + ))
       ; ("mult", IntOp2 ( * ))
       ; ("initial", State (initial_state ~max_color))
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

   let lookup ~max_color = Hashtbl.find_exn @@ graph_values ~max_color

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
         failwith "Graphs.evaluator: apply of for_i to non-integer" *)

let initial_primitives_types_alist ~max_color =
  ( List.range 0 @@ max 10 max_color
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

let initial_primitives_list ~max_color =
  initial_primitives_types_alist ~max_color
  |> List.map ~f:(fun (name, ty) -> Primitive {name; ty})

let initial_primitives ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map ~f:(fun (name, ty) -> (name, Primitive {name; ty}))
  @@ initial_primitives_types_alist ~max_color

let initial_dsl ~max_color =
  dsl_of_primitives graph_state @@ initial_primitives_list ~max_color

let initial_primitive_entries ~max_color =
  Hashtbl.of_alist_exn (module String)
  @@ List.map (initial_dsl ~max_color).library ~f:(fun ent -> (ent.name, ent))

(* let rec reduce_identity identity_type = function
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

   let evaluate_with_initial ~max_color =
     evaluate
       ~preprocess:(reduce_identity graph_transform)
       naturalize (lookup ~max_color) eval
       [Primitive {name= "initial"; ty= graph_state}]

   let evaluate ~max_color ~timeout ~attempts p =
     Option.value_map ~default:None ~f:Fn.id
     @@ Util.run_for_interval ~attempts timeout (fun () ->
            try
              match evaluate_with_initial ~max_color p with
              | Some (State out) ->
                  Some out
              | _ ->
                  failwith
                  @@ Format.sprintf
                       "evaluate: graph program did not output a state: %s"
                       (string_of_program p)
            with e ->
              Format.eprintf "ERROR: %s\n" @@ string_of_program p ;
              raise e ) *)
