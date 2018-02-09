type tyvar = Var of string
type tyname = Name of string
type mode = Sep
          | Ind
          | Deepsep

type ty = Unit
        | Int
        | Float
        | Bool
        | Char
        | Arrow of (ty * ty)
        | Cons of (ty * ty)
        | Or of (ty * ty)
        | Tyvar of tyvar
        | Param of (ty list * tyname)
        | Exists of tyvar * ty
        | Abstract of tyname

type def = Def of (tyvar * mode) list * tyname * ty * mode

type test = string * (def list) * bool

exception Existential_is_not_sep of tyvar

let rec print_ty (u : ty) = 
  let rec aux t = match t with
    | Unit | Int | Float | Bool | Char -> print_string "base"
    | Arrow (a, b) -> let _ = aux a in let _ = print_string " -> " in aux b
    | Cons (a, b) -> let _ = aux a in let _ = print_string " : " in aux b
    | Or (a, b) -> let _ = aux a in let _ = print_string " | " in aux b
    | Tyvar (Var a) -> print_string a
    | Param (a, b) ->
       let print c d =
         let _ = print_string "param" in
         let _ = (List.iter (fun x -> print_ty x) c) in
         let _ = begin match d with Name s -> print_string s end in
         let _ = (print_string "(")
         in let _ = (aux u)
            in print_string ")\n"
       in (print a b)
    | Exists (a, b) ->
       let _ = print_string "exists"
       in let _ = begin match a with Var c -> print_string c end
          in (print_ty b)
    | Abstract _ -> ()
  in aux u;;

Random.self_init ();;

let rec rand_ty a =
  let n = (Random.int 7) in
  match n with
  | 0 -> Int
  | 1 -> (Arrow (rand_ty a, rand_ty a))
  | 2 -> (Cons (rand_ty a, rand_ty a))
  | 3 -> (Tyvar (Var " a "))
  | 4 -> (Param ((Tyvar (Var " b ") :: Arrow (Int, Float) :: []), Name "e"))
  | 5 -> (Exists ((Var "c"), rand_ty ()))
  | 6 -> (Or (rand_ty (), rand_ty ()))
  | _ -> Int;;

let rec rand_tyvars n = match n with
  | 0 -> []
  | a -> ((Var (String.make 1 (Char.chr (Random.int 255)))), Ind) :: (rand_tyvars (n - 1));;

let rand_def a = 
  Def (rand_tyvars (Random.int 10), (Name (String.make 1 (Char.chr (Random.int 255)))), rand_ty (), Sep);;

let rec rand_defs n = match n with
  | 0 -> []
  | a -> (rand_def 1) :: (rand_defs (a - 1));;

let rec rand_tys a = match a with
  | 1 -> (rand_ty ()) :: []
  | b -> (rand_ty ()) :: (rand_tys (b - 1));;



let get_def (tofind : tyname) (defs : def list) =
  List.find (fun (Def (_, name, _, _)) -> name = tofind);;

let rec replace_def (defs : def list) (olddef : def) (newdef :def) =
  match defs with
  | [] -> []
  | hd :: tl when hd = olddef -> newdef :: tl
  | hd :: tl -> hd :: (replace_def tl olddef newdef);;

let rec update_def (d : def) (l : (tyvar * mode) list) =
  match d with Def (tym, name, bod, mode) -> Def ((List.map (fun (a, b) -> if List.mem_assoc a l then (a, List.assoc a l) else (a, b)) tym), name, bod, mode);;

let get_ty_mode (name : tyname) (defs : def list) =
  match (List.find (fun (Def (_, x, _, _)) -> name = x) defs) with Def(tym, _, _, _) -> tym;;


let mode_union a b = match a, b with
  | (Ind, Ind) -> Ind
  | (Sep, Sep) -> Sep
  | (Sep, Ind) | (Ind, Sep) -> Sep
  | (Deepsep, _) | (_, Deepsep) -> Deepsep

let mode_inc a b = match a, b with
  | (Ind, _) | (Sep, Deepsep) | (Deepsep, Deepsep) | (Sep, Sep) -> true
  | _ -> false

let mode_point a b = match a, b with
  | (Deepsep, _) | (_, Deepsep) -> Deepsep
  | (Ind, _) | (_, Ind) -> Ind
  | (a, b) -> a




let rec check_type (tocheck : ty) (defs : def list) (m : mode) =
  if m = Ind then [] else
    match tocheck with
    | Unit | Int | Float | Bool | Char -> []
    | Arrow (a, b) | Cons (a, b) | Or (a, b) ->
       let outa = (check_type a defs m) in
       let outb = (check_type b defs m) in
       List.append outa outb
    | Tyvar a -> [(a, m)]
    | Param (par, name) -> check_args par defs (get_ty_mode name defs)
    | Exists (ex, bod) -> begin
        let out = check_type bod defs m in
        try if List.assoc ex out = Ind then raise (Existential_is_not_sep ex)
            else out
        with Not_found -> out
      end
    | Abstract par -> []
                            
                            
                            
and check_args (par : ty list) (defs : def list) (d : (tyvar * mode) list) =
  let rec aux (l : (ty * mode) list) =
    match l with
    | [] -> []
    | (hdty, hdm) :: tl -> List.append (check_type hdty defs hdm) (aux tl) in
  let l = (List.map2 (fun x (y,z) -> (x, z)) par d) in
  aux l


and check_def (tocheck : def) (defs : def list) (m : mode) =
  match tocheck with
    Def (partc, nametc, tytc, modetc) ->
     match tytc with
     | Unit | Int | Float | Char |Bool -> []
     | Arrow (_, _) | Cons (_, _) | Or (_, _) | Param (_, _) | Exists (_, _) | Tyvar _ | Abstract _ -> (check_type tytc defs (mode_point m Ind))
                                                                                                                      


let check (defs : def list) =
  let rec aux (todo : def list) (defs : def list) =
    match todo with
    | [] -> defs
    | hd :: tl ->
       begin
         match (check_def hd defs Sep) with
         | [] -> aux tl defs
         | a -> aux defs (replace_def defs hd (update_def hd a))
       end
  in aux defs defs;;

let existential_pass = ("type ex_acc = E : ('a -> int) -> ex_acc", [Def ([], Name "ex_acc", Exists (Var "a", Arrow (Tyvar (Var "a"), Int)), Sep)], true)

let existential_fail = ("type ex_rej = E : 'a -> ex_rej", [Def ([], Name "ex_rej", Exists (Var "a", Tyvar (Var "a")), Sep)], false)

let existential_absent = ("type ex_abs = E : unit -> ex_abs", [Def ([], Name "ex_abs", Exists (Var "a", Unit), Sep)], true)

let recursive_1 = ("type ('a, 'b) t = 'a \nand ('c, 'd) u = ('c, 'd) t", [Def ([(Var "a", Ind); (Var "b", Ind)], Name "t", Tyvar (Var "a"), Sep); Def ([(Var "c", Ind); (Var "d", Ind)], Name "u", Param ([Tyvar (Var "c"); Tyvar (Var "d")], Name "t"), Sep)], true)

let tree = ("type ('a, 'k) tree = bool -> 'a node \nand 'a node = N : ('a, 'k) tree", [Def ([(Var "a", Ind); (Var "k", Ind)], Name "tree", Arrow (Bool, Param ([Tyvar (Var "a")], Name "node")), Sep); Def ([Var "a", Ind], Name "node", Exists (Var "k", Param ([Tyvar (Var "a"); Tyvar (Var "k")], Name "tree")), Sep)], true)

let recursive_self = ("type 'a self = 'a self", [Def ([(Var "a", Ind)], Name "self", Param ([Tyvar (Var "a")], Name "self"), Sep)], true)

let inclus = ("type 'a t : ind and u = bool t", [Def ([(Var "a", Ind)], Name "t", Unit, Ind); Def ([], Name "u", Param ([Bool], Name "t"), Ind)], true)

let deepsep_fail = ("type 'a t and u = U : (b -> int) t -> e", [
                      Def ([(Var "a", Ind)], Name "t", Abstract (Name "t"), Deepsep);
                      Def ([], Name "u", Exists (Var "b", Param ([Arrow (Tyvar (Var "b"), Int)], Name "t")), Ind)], false)

let deepsep_fail_big = ("type 'a t : Deepsep and u = U : (b -> int) w -> u and 'c w = ('c -> bool) * int", [
                      Def ([(Var "a", Deepsep)], Name "t", Abstract (Name "t"), Deepsep);
                      Def ([], Name "u", Exists (Var "b", Param ([Arrow ((Tyvar (Var "b")), Int)], Name "w")), Ind);
                      Def ([(Var "c", Ind)], Name "w", Cons (Param ([Arrow ((Tyvar (Var "c")), Bool)], Name "t"), Int), Ind)], false)

let deepsep_pass = ("type 'a t : Deepsep and 'b u = (b -> int) w and 'c w = ('c -> bool) * int", [
                      Def ([(Var "a", Deepsep)], Name "t", Abstract (Name "t"), Deepsep);
                      Def ([(Var "b", Ind)], Name "u", Param ([Arrow ((Tyvar (Var "b")), Int)], Name "w"), Ind);
                      Def ([(Var "c", Ind)], Name "w", Cons (Param ([Arrow ((Tyvar (Var "c")), Bool)], Name "t"), Int), Ind)], true)
                  

let test (case : test) =
  let success str = print_string (str ^ "   -   test passed\n") in
  let failure str = print_string (str ^ "   -   test failed\n") in
  match case with
    (str, defs, pass) ->
    try let _ = (check defs) in if pass then success str else failure str
    with Existential_is_not_sep e -> if pass then failure str else success str;;

let _ = test existential_pass

let _ = test existential_fail

let _ = test existential_absent

let _ = test recursive_1

let _ = test tree

let _ = test recursive_self

let _ = test inclus

let _ = deepsep_fail

let _ = deepsep_fail_big          

let _ = deepsep_pass
