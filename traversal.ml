open Core
open Antireduce

type t = Util.IntPair.t option list
[@@deriving equal, compare, sexp_of, hash, yojson]
