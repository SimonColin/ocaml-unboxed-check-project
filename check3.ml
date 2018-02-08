type tyvar = Var of string;;
type tyname = Name of string;;
type mode = Sep | Ind;; (* | Deepsep;; *)

type ty = Unit | Int | Float | Bool | Char | Arrow of (ty * ty) | Cons of (ty * ty) | Or of (ty * ty) | Tyvar of tyvar | Param of (ty list * tyname) | Exists of tyvar * ty;;

type context = (tyvar * mode) list;;

type def = Def of (tyvar * mode) list * tyname * ty * mode;;

exception Existential_is_not_sep of tyvar;;

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
  in aux u;;

let rec print_ctx (ctx : context) =
  let print_mode (m : mode) =
    match m with
    | Sep -> print_endline "sep"
    | Ind -> print_endline "ind"
                           (* | Deepsep -> print_endline "deepsep" *)
  in
  match ctx with
  | [] -> ()
  | (Var name, mode) :: tl -> let _ = print_string name in let _ = print_mode mode in let _ = print_newline in print_ctx tl;;

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
(*
let rec tynames n = match n with
  | [] -> []
  | Def (tm, tyn, t, _) :: b -> tyn :: tynames b;; *)

let get_mode (c : context) (t : tyvar) = if List.mem (t, Sep) c then Sep else
                                       Ind;;
(*
let getmodefromdef (d : def list) (t : tyvar) (a : ty) =
  try let definition = (List.find (fun (Def (x, y, z, _)) -> z = a) d)
      in match definition with Def (tym, tyn, l, _) ->
                            if List.mem (t, Sep) tym then Sep else Ind
  with Not_found -> assert false;; *)

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


let mode_union = function
  | (Ind, Ind) -> Ind
  | (Sep, Sep) -> Sep
  | (Sep, Ind) | (Ind, Sep) -> Sep
(*  | (Deepsep, _) | (_, Deepsep) -> Deepsep *)





let rec check_type (defs : def list) (ctx : context) (t : ty) (m : mode) =
  if m = Ind then Ind else
    match t with
    | Unit | Int | Float | Bool | Char -> m
    | Arrow (_, _) | Cons (_, _) -> m
    | Or (a, b) -> mode_union ((check_type defs ctx a m), (check_type defs ctx b m))
    | Tyvar a -> (get_mode ctx a)
    | Param (par, name) -> if check_args par defs (get_ty_mode name defs) ctx = [] then m else Ind
    | Exists (ex, bod) -> let def = Def ([], Name "", bod, m) in
                          let out = (check_def def defs ctx m) in
                          if (List.assoc ex out) = Sep
                          then raise (Existential_is_not_sep ex)
                          else if out = [] then m else Ind
                                                         
                                                         
and check_args (par : ty list) (defs : def list) (d : (tyvar * mode) list) (ctx : context) =
  let rec aux (l : (ty  * mode) list) =
    match l with
    | [] -> []
    | (p, md) :: tl when check_type defs ctx p md = md -> aux tl
    | (Tyvar a, md) :: tl -> (a, md) :: (aux tl)
    | (_, _) :: tl -> assert false (* aux tl *)
  in
  aux (List.map2 (fun x (y, z) -> (x, z)) par d) (*let m = if  then Sep else Ind in (x, (check_type defs ctx x Sep), y, z)) par d) *)


and check_def (tocheck : def) (defs : def list) (ctx : context) (m : mode) =
  let check_exists (tocheck : def) (defs : def list) (ctx : context) (m : mode) =
    match (check_def tocheck defs ctx m) with
    | [] -> []
    | a -> List.append a (check_def tocheck defs (List.append a ctx) m) in
  match tocheck with
    Def (partocheck, nametocheck, tytocheck, mode) ->
     match tytocheck with
     | Unit | Int | Float | Bool | Char -> []
     | Arrow (_, _) | Cons (_, _) -> []
     | Or (a, b) -> let defa = (Def (partocheck, nametocheck, a, mode)) in
                    let defb = (Def (partocheck, nametocheck, a, mode)) in
                    let outa = (check_def defa (replace_def defs tocheck defa) ctx m) in
                    let outb = (check_def defb (replace_def defs tocheck defb) (List.append outa ctx) m) in
                    List.append  outa outb
     | Tyvar a -> if List.mem (a, Sep) ctx then [] else (a, Sep) :: []
     | Param (par, name) -> check_args par defs (get_ty_mode name defs) ctx
     | Exists (ex, bod) -> begin
         let newtocheck = Def ([], nametocheck, bod, mode) in
         let newdefs = replace_def defs tocheck newtocheck in
         let out = (check_exists newtocheck newdefs ((ex, Ind) :: ctx) m) in
         if List.mem (ex, Sep) out then raise (Existential_is_not_sep ex) else out
       end;;



let check (defs : def list) (ctx : context) =
  let rec aux (todo : def list) (defs : def list) (ctx : context) =
    match todo with
    | [] -> ctx
    | hd :: tl ->
       begin
         match (check_def hd defs ctx Sep) with
         | [] -> aux tl defs ctx
         | a -> aux defs (replace_def defs hd (update_def hd a)) (List.append ctx a)
       end
  in aux defs defs ctx;;

(* let defs = (Def ([], Name "def1", Int, Sep))
           :: ((Def (([(Var "a", Ind); (Var "b", Ind)]), (Name "def2"), (Tyvar (Var "b")), Sep))
               :: ((Def (([(Var "c", Ind); (Var "d", Ind)]), (Name "def3"), (Param (([(Var "c"); (Var "d")]), (Name "def2"))), Sep))
                   :: (Def ([], (Name "def4"), (Exists (Var "e", Tyvar (Var "e"))), Sep)) :: [])) *)

let existential_accept = Def ([], Name "ex_acc", Exists (Var "a", Arrow (Tyvar (Var "a"), Int)), Sep)

let existential_reject = Def ([], Name "ex_rej", Exists (Var "a", Tyvar (Var "a")), Sep)

let existential_absent = Def ([], Name "ex_abs", Exists (Var "a", Unit), Sep)

let recursive_1 = Def ([(Var "a", Ind); (Var "b", Ind)], Name "t", Tyvar (Var "a"), Sep)

let recursive_2 = Def ([(Var "c", Ind); (Var "d", Ind)], Name "u", Param ([Tyvar (Var "c"); Tyvar (Var "d")], Name "t"), Sep)

let tree = Def ([(Var "a", Ind); (Var "k", Ind)], Name "tree", Arrow (Bool, Param ([Tyvar (Var "a")], Name "node")), Sep)

let node = Def ([Var "a", Ind], Name "node", Exists (Var "k", Param ([Tyvar (Var "a"); Tyvar (Var "k")], Name "tree")), Sep)

let recursive_self = Def ([(Var "a", Ind)], Name "self", Param ([Tyvar (Var "a")], Name "self"), Sep)
                
let ctx = [];;

let test (defs : def list) =
  let print_tyvar (a : tyvar) = match a with
      Var str -> print_string (str ^ " not Sep") in
  try print_ctx (check defs ctx)
  with Existential_is_not_sep e -> print_tyvar e;;

let _ = test (existential_accept :: [])

let _ = test (existential_reject :: [])

let _ = test [existential_absent]

let _ = test [recursive_1; recursive_2]

let _ = test [tree; node]

let _ = test [recursive_self]

          
