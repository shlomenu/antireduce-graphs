open Core

type t = Forward | Backward [@@deriving yojson]

let reverse = function Forward -> Backward | Backward -> Forward
