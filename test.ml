
(* unboxed example *)
type name = Name of string [@@unboxed]

let float_array = Array.create_float 10;;

let int_array = Array.make 10 1;;

(* seg fault example *)

let array = Array.make_float 3;;

Array.set array 1 (Obj.magic 1);;

(* GADT with existentail *)

type ext = E : 'a -> ext [@@unboxed];;

type ('a, 'b) t = 'a and ('c, 'd) u = ('c, 'd) t;;

(* constraint example *)

type 'a t = 'b constraint 'a = 'b * 'c
and type ext = E : 'a -> ext
and type c = C of ext * int
type not_unboxable = c t [@@unboxed];;

(* In this case C is of the shape a * b hence it is Sep if a : sep and b : sep which is the case however not_unboxable is not sep since ext is not. *)

(* existential examples *)

type 'a sep = S : 'b * 'a -> sep;;

(* is checked by seeing if *)

type ('a, 'b) sep = S of 'b * 'a (* can be sep without requiring 'b to be sep *)

type notsep = N : 'a -> notsep;;

(* is checkde by seeing if *)

type 'a notsep = 'a;; (* can be sep without requiring 'a to be sep *)

