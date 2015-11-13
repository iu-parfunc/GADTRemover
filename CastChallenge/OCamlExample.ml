

let x = 3

let y = "hi"


type bytes    = Blah of unit
type 'a array = Blah2 of unit

type 'a t = | Array : 'a array -> 'a t
            | Bytes : bytes -> 'a t


type ('a,'e) exp = | Con : int -> (int,'e) exp
