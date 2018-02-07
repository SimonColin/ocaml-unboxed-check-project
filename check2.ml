type tyvar = Var of string;;
type tyname = Name of string;;
type mode = Sep | Ind;;

type ty = Unit | Int | Float | Bool | Char | Arrow of (ty * ty) | Cons of (ty * ty) | Tyvar of tyvar | Param of (tyvar list * tyname) | Exists of tyvar * ty;;

type context = (tyvar * mode) list;;(* Nil | Cons of ((tyvar * mode) * (tyvar * mode));;*)

type def = Def of (tyvar * mode) list * tyname * ty * mode;;

exception Existential_is_not_sep of tyvar;;

let rec print_ty (u : ty) = 
  let rec aux t = match t with
    | Unit | Int | Float | Bool | Char -> print_string "base"
    | Arrow (a, b) -> let _ = aux a in let _ = print_string " -> " in aux b
    | Cons (a, b) -> let _ = aux a in let _ = print_string " : " in aux b
    | Tyvar (Var a) -> print_string a
    | Param (a, b) -> let print c d = let _ = print_string "param" in
                                      let _ = (List.iter (fun (Var x) -> print_string x) c)
                                         in let _ = begin match d with Name s -> print_string s end
                                            in let _ = (print_string "(")
                                               in let _ = (aux u)
                                                  in print_string ")\n"
                      in (print a b)
    | Exists (a, b) -> let _ = print_string "exists"
                       in let _ = begin match a with Var c -> print_string c end
                          in (print_ty b)
  in aux u;;
                                           

Random.self_init ();;

let rec rand_ty a =
  let n = (Random.int 6) in match n with
                            | 0 -> Int
                            | 1 -> (Arrow (rand_ty a, rand_ty a))
                            | 2 -> (Cons (rand_ty a, rand_ty a))
                            | 3 -> (Tyvar (Var " a "))
                            | 4 -> (Param ((Var " b " :: Var " c " :: []), Name "e"))
                            | 5 -> (Exists ((Var "c"), rand_ty ()))
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

let rec tynames n = match n with
  | [] -> []
  | Def (tm, tyn, t, _) :: b -> tyn :: tynames b;;

let getmode (c : context) (t : tyvar) = if List.mem (t, Sep) c then Sep else
                                       Ind;;

let getmodefromdef (d : def list) (t : tyvar) (a : ty) =
  try let definition = (List.find (fun (Def (x, y, z, _)) -> z = a) d)
      in match definition with Def (tym, tyn, l, _) ->
                            if List.mem (t, Sep) tym then Sep else Ind
  with Not_found -> assert false;;


let check (d : def list) (c : context) (t : ty) (m : mode) =
  let rec check_args (l : tyvar list) (defi: def) =
    match l with
    | [] -> []
    | a :: b -> match defi with Def (tm, _, _, _) -> if List.mem (a, getmodefromdef d a t) c 
                                                  then check_args b defi
                                                  else a :: check_args b defi
  in match t with
     | Unit | Int | Float | Bool | Char -> []
     | Arrow (_, _) | Cons (_, _) -> []
     | Tyvar a -> if List.mem (a, m) c then [] else a :: []
     | Param (a, b) -> check_args a (List.find (fun (Def (_, x, _, _)) -> x = b) d)
     | Exists (ex, corps) -> begin match check_args (ex :: [])  with
                        | Tyvar a -> raise (Existential_is_not_sep a)
                        | _ -> []
                        end;;

let rec update (ctx : context) (t : tyvar) =
  match ctx with
  | (a, b) :: c when a = t -> (a, Sep) :: (update c t)
  | a :: b -> a :: (update b t)
  | [] -> [];;

let checkAll (d : def list) = 
  let rec checkdef (defs : def list) (c : context) =
    begin match defs with
    | a :: b -> (match a with Def (l, n, t, m) -> let out = (check d c t m) in if out = [] then checkdef b c else (update c out))
    | [] -> []
    end
let checkdefs (d : def list) (c : context) =
  match (checkdef d c) with
  | [] -> []
  | a -> (checkdef d a)
in checkdefs d [];;

           (* let defs = rand_defs 10 in List.iter (fun (Name x) -> print_string
   x) (tynames defs);; *)
           (* List.iter (fun x -> print_ty x) (rand_tys 6);; *)

           (* let check_def (d : def) =

let check (d : def) (c : context) (t : ty) (m : mode) = *)
