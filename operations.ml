open Core

let identity : State.t -> State.t = Fn.id

let next_port (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with port= (s.port + 1) mod s.graph.max_conn}

let prev_port (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with port= (if s.port = 0 then s.graph.max_conn - 1 else s.port - 1)}

let port_func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) =
  g {(f s) with port= s.port}

let pos_func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) :
    State.t =
  g {(f s) with pos= s.pos}

let func (f : State.t -> State.t) (g : State.t -> State.t) (s : State.t) :
    State.t =
  g {(f s) with port= s.port; pos= s.pos}

let if_positions_equal (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (k : State.t -> State.t) (l : State.t -> State.t)
    (s : State.t) : State.t =
  l (if State.pos (f s) = State.pos (g s) then h s else k s)

let move (f : State.t -> State.t) (s : State.t) : State.t =
  f {s with pos= Option.value_map (State.selected s) ~default:s.pos ~f:Fn.id}

let add_nb (f : State.t -> State.t) (s : State.t) =
  f
    { s with
      graph=
        ( if Option.is_none (State.selected s) then
          let nb, g' = Graph.add_node s.graph in
          Graph.add_edge s.port g' s.pos nb
        else s.graph ) }

let add_conn (f : State.t -> State.t) (g : State.t -> State.t)
    (h : State.t -> State.t) (s : State.t) : State.t =
  h
    { s with
      graph= Graph.add_edge s.port s.graph (State.pos (f s)) (State.pos (g s))
    }

let last_found : Graph.t option ref = ref None

let save (s : State.t) : State.t =
  last_found := Some s.graph ;
  s
