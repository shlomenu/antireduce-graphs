open Core

let reorient (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with dir= Direction.reverse @@ State.dir s}

let next (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with color= (s.color + 1) mod s.graph.max_color}

let set_color_under_cursor (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with color= Map.find_exn s.graph.nodes s.loc}

let reset_color (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with color= 0}

let reset_cursor (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with loc= 0}

let traverse (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with loc= Option.value_map (State.selected s) ~default:s.loc ~f:Fn.id}

let add (f : State.t -> State.t) (s : State.t) =
  f
    { s with
      graph=
        ( if Option.is_none (State.selected s) then
          let nb, g' = Graph.add_node s.graph s.color in
          Graph.add_edge s.dir g' s.loc nb
        else s.graph ) }

let if_traversable (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (s : State.t) : State.t =
  if Option.is_some @@ State.selected s then f (g s) else f (h s)

let if_current (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (s : State.t) : State.t =
  if equal s.color @@ Map.find_exn s.graph.nodes s.loc then f (g s) else f (h s)

let connect (f : State.t -> State.t) (s : State.t) : State.t =
  f
    { s with
      graph=
        Option.value_map ~default:s.graph
          ~f:(Graph.add_edge s.dir s.graph s.loc)
        @@ List.hd s.positions }

let push_pos (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with positions= s.loc :: s.positions}

let pop_pos (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with positions= List.drop s.positions 1}

let push_color (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with colors= s.color :: s.colors}

let pop_color (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with colors= List.drop s.colors 1}

let for_i (i : int) (g : State.t -> State.t) (f : State.t -> State.t)
    (s : State.t) : State.t =
  f @@ List.fold (List.range 0 i) ~init:s ~f:(fun s' _ -> g s')

let pos_proc (g : State.t -> State.t) (f : State.t -> State.t) (s : State.t) :
    State.t =
  f {(g {s with positions= []}) with positions= s.positions}

let color_proc (g : State.t -> State.t) (f : State.t -> State.t) (s : State.t) :
    State.t =
  f {(g {s with colors= []}) with colors= s.colors}

let last_found : Graph.t option ref = ref None

let save (s : State.t) : State.t =
  last_found := Some s.graph ;
  s

(*

    --- API rewrite, kept separate for backwards compatibility ---

   Some functions are simply renamed and some are obsolesced, but no name
   clashes are introduced.
*)

let identity : State.t -> State.t = Fn.id

let switch_direction = reorient

let select_next = next

let select_prev (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with color= (if s.color = 0 then s.graph.max_color - 1 else s.color - 1)}

let read_color = set_color_under_cursor

let color_func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) =
  g {(f s) with color= s.color}

let loc_func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) :
    State.t =
  g {(f s) with loc= s.loc}

let dir_func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) :
    State.t =
  g {(f s) with dir= s.dir}

let func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) :
    State.t =
  g {(f s) with color= s.color; loc= s.loc; dir= s.dir}

let if_colors_equal (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (k : State.t -> State.t) (l : State.t -> State.t)
    (s : State.t) : State.t =
  l (if State.color (f s) = State.color (g s) then h s else k s)

let if_locs_equal (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (k : State.t -> State.t) (l : State.t -> State.t)
    (s : State.t) : State.t =
  l (if State.loc (f s) = State.loc (g s) then h s else k s)

let move_selected = traverse

let add_nb = add

let add_conn (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (s : State.t) : State.t =
  h
    { s with
      graph= Graph.add_edge s.dir s.graph (State.loc (f s)) (State.loc (g s)) }
