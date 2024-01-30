type op  = Add | Sub | Mul | Leq | Arrow
type ty  = Int | Bool | Arrow of ty * ty (*EP.2 b*)
type exp = Icon of int | Bcon of bool | Var of string | Ty of ty
         | Binary of op * exp * exp
         | If of exp * exp * exp
         | Let of string * exp * exp
         | App of exp * exp (*EP.2 a*)
         | Lam of string * ty * exp (*EP.2 a*)
         | Letrec of string * string * ty * ty * exp * exp (*EP.2 a*)

(* environments *)
let rec lookup k env = match env with
  | [] -> None
  | (k', v) :: l -> if k = k' then Some v else lookup k l
  
let rec update k v env = match env with
  | [] -> [(k, v)]
  | (k', v') :: l -> if k = k' then (k, v) :: l else (k', v') :: update k v l

type 'b env = (string * 'b) list

(* type checking *)
type tenv = ty env

let rec check_ty (env : tenv) (e : exp) =
  let ty_eq t1 t2 = match t1, t2 with
    | Some t1, Some t2 -> t1 = t2
    | _, _ -> false in
  match e with
  | Icon _ -> Some Int
  | Bcon _ -> Some Bool
  | Var x -> lookup x env
  | If (e1, e2, e3) -> let t1 = check_ty env e1 in
                       let t2 = check_ty env e2 in
                       let t3 = check_ty env e3 in
                       if ty_eq t1 (Some Bool) && ty_eq t2 t3
                       then t2 else None
  | Let (x, e1, e2) -> let t1 = check_ty env e1 in             
                       (match t1 with 
                         | Some t1 -> 
                            let env' = update x t1 env in
                            check_ty env' e2
                         | None -> None)
  | Binary (op, e1, e2) ->  let t1 = check_ty env e1 in
                            let t2 = check_ty env e2 in
                            if ty_eq t1 (Some Int) 
                            && ty_eq t2 (Some Int) 
                            then Some (match op with 
                                       | Leq -> Bool
                                       | _ -> Int)
                            else None
  | Lam (x, t1, e2) -> let env' = update x t1 env in (*EP.3 a*)
                       let t2 = check_ty env' e2 in
                       (match t2 with
                        | Some t2 -> Some (Arrow (t1, t2))
                        | None -> None)
  | App (e1, e2) ->   let t1 = check_ty env e1 in (*EP.3 a*)
                      let t2 = check_ty env e2 in
                      (match t1, t2 with
                        | Some Arrow(t2', t), Some t2 -> if t2' = t2 then Some t else None
                        | _, _ -> None
                      )
  | Letrec (f, x, t1, t2, e1, e2) -> let env' = update x t2 (update f (Arrow (t1, t2)) env) (*EP.3 a*)
                                     in let t_e1 = check_ty env' e1 
                                     in let env'' = update f (Arrow (t1, t2)) env 
                                     in let t_e2 = check_ty env'' e2 
                                     in (match t_e1 with
                                          | Some t_e1 -> if t_e1 = t2 then t_e2 else None
                                          | None -> None)
                                                                         

(* Evaluator *)
type va = Ival of int | Bval of bool 
        | Cl of string * exp * venv
        | Cr of string * string * exp * venv
and venv = va env

let rec eval (env : venv) (e : exp) = match e with
  | Icon c -> Ival c
  | Bcon b -> Bval b
  | Var x  -> (match lookup x env with 
                 | Some v -> v 
                 | None -> failwith ("no value for var " ^ x))
  | If (e1, e2, e3) -> (match eval env e1 with
                        | Bval true -> eval env e2
                        | Bval false -> eval env e3
                        | _ -> failwith "if cond non-bool")
  | Let (x, e1, e2) -> let v = eval env e1 in
                       let env' = update x v env in
                       eval env' e2
  | Binary (op, e1, e2) -> let v1 = eval env e1 in
                           let v2 = eval env e2 in
                           (match op, v1, v2 with
                           | Add, Ival x, Ival y -> Ival (x + y)
                           | Sub, Ival x, Ival y -> Ival (x - y)
                           | Mul, Ival x, Ival y -> Ival (x * y)
                           | Leq, Ival x, Ival y -> Bval (x <= y)
                           | _ -> failwith "illegal val in bin op")
  | Lam (x, t1, e2) -> Cl (x, e2, env) (*EP.3 b*)
  | Letrec (f, x, t1, t2, e1, e2) -> let env' = update f (Cr (f, x, e1, env)) env (*EP.3 b*)
                                     in eval env' e2
  | App (e1, e2) -> match (eval env e1) with (*EP.3 b*)
                      | Cl (x, e, v) -> let v2 = eval env e2 
                        in eval (update x v2 v) e
                      | Cr (f, x, e, v) -> let v2 = eval env e2 
                        in eval (update x v2 (update f (Cr (f, x, e, v)) v)) e
                      | _ -> failwith "e1 is not a function and can't be applied to e2"

;;

(* lexer *)
type token = ADD | SUB | MUL | LEQ 
           | LP | RP | EQ | ARROW
           | LET | REC | IN | FUN | IF | THEN | ELSE 
           | INT | BOOL
           | VAR of string | ICON of int | BCON of bool
           | COL | GR | LE | END_OF_INPUT(*EP.1 b, GR and LE only works for the lexer*)
           
let lex s = 
  let whitespace c = match c with
    | ' ' | '\n' | '\t' -> true
    | _ -> false in
  let lc_letter c = match c with
    | 'a' .. 'z' -> true
    | _ -> false in
  let id_rest c = match c with
    | 'A' .. 'Z' | 'a' .. 'z' | '_' | '\'' | '0' .. '9' -> true
    | _ -> false in
  let digit c = match c with
    | '0' .. '9' -> true
    | _ -> false in
    
  
  let n = String.length s in
  let get i = String.get s i in
  
  (*
  EP.1 a
  Funtion to return all positive digits
  *)
  let to_int c = Char.code c - Char.code '0' in
  
  let rec get_digits i d = 
    if i >= n then (d, i)
    else if digit (get i) 
      then let di = d * 10 + to_int(get i) in get_digits (i + 1) di 
      else (d, i)
      in
  
  (*
  Function to ignore comments
  *)
  let rec ignore_comments i =
    if i+1 >= n then failwith "Comment not terminated"
    else 
      if get (i) = '*' && get (i + 1) = ')' 
      then (i+2)
      else ignore_comments (i+1) in

  
  let rec lex_id i j l = 
    if j >= n then id_classify (String.sub s i (j - i)) j l else 
    match get j with 
    | c when id_rest c -> lex_id i (j + 1) l
    | _ -> id_classify (String.sub s i (j - i)) j l
    
  
  and id_classify s i l =
    let t = match s with 
    | "let" -> LET
    | "rec" -> REC (*added*)
    | "fun" -> FUN (*added*)
    | "in" -> IN
    | "if" -> IF
    | "then" -> THEN
    | "else" -> ELSE
    | "true" -> BCON true
    | "false" -> BCON false
    | "int" -> INT (*added*)
    | "bool" -> BOOL (*added*)
    | _ -> VAR s
    in work i (t :: l)
  
  and work i l = 
    if i >= n then l else
    if whitespace (get i) then work (i + 1) l else
    match get i with
    | ';' -> work (i + 1) (END_OF_INPUT :: l)
    | '+' -> work (i + 1) (ADD :: l)
    | '>' -> work (i + 1) (GR :: l) (* GR only works for the lexer and not on any other level like parsing, type-checking or evaluating*)
    | '-' -> if i + 1 < n && get (i + 1) = '>'
             then work (i + 2) (ARROW :: l)
             else work (i + 1) (SUB :: l)
    | '*' -> work (i + 1) (MUL :: l)
    | '(' -> if i + 1 < n && get (i + 1) = '*'
             then work (ignore_comments (i + 2)) l
             else work (i + 1) (LP :: l)
    | ')' -> work (i + 1) (RP :: l)
    | '=' -> work (i + 1) (EQ :: l)
    | '<' -> if i + 1 < n && get (i + 1) = '=' 
             then work (i + 2) (LEQ :: l)
             else work (i + 1) (LE :: l) (* LE only works for the lexer and not on any other level like parsing, type-checking or evaluating*)
    | ':' -> work (i + 1) (COL :: l) (*added*)
    | c when lc_letter c -> lex_id i i l
    | c when digit c -> let (d, j) = get_digits i 0 in work (j) (ICON d :: l) (*added*)
    | _ -> failwith "illegal character"
  in List.rev (work 0 [])
  
;;
lex "int bool  + 102 abc aB'_ true let ( )<==->* -*<= -->def 15 (*ignored*)"
;;

(* parser *)

(* operator precedence parser *)
let parse_binary parse_simple_expr parse_op ts = 
  let rec binary p (l, ts) =
    match parse_op ts with
      | None -> (l, ts)
      | Some (op, lp, rp, ts') -> 
        if lp < p then (l, ts) else
          let r, ts = binary rp (parse_simple_expr ts')
          in binary p (op l r, ts)
in binary 0 (parse_simple_expr ts)

let expect_id ts = match ts with
  | VAR x :: ts -> x, ts
  | _ -> failwith "identifier expected"  
  
let expect t ts = match ts with
  | t' :: ts when t = t' -> ts
  | _ -> failwith "Parse error"

let rec ex_in_paren ts l = (*EP.2 e*)
  match ts with
    | [] -> failwith "parenthesis mismatch"
    | LP :: ts -> let l_in_p, t = ex_in_paren ts [] 
                 in ex_in_paren t (l @ ([LP]@l_in_p@[RP]))
    | h :: ts -> if h = RP then l, ts else ex_in_paren ts (l @ [h])

let parse_op ts =
  let create op l r = Binary (op, l, r) in 
  let create_ar (Ty l) (Ty r) = Ty (Arrow (l, r)) in (*added*)
  let create_fap l r = App (l, r) in (*added*)
  match ts with
  | LEQ :: ts -> Some (create Leq, 0, 1, ts)
  | ADD :: ts -> Some (create Add, 2, 3, ts)
  | SUB :: ts -> Some (create Sub, 2, 3, ts)
  | MUL :: ts -> Some (create Mul, 4, 5, ts)
  | ARROW :: ts -> Some (create_ar, 5, 6, ts) (*EP.2 c*)
  | VAR x :: ts -> Some (create_fap, 7, 8, VAR x :: ts) (*EP.2 d*)
  | ICON x :: ts -> Some (create_fap, 7, 8, ICON x :: ts)
  | LP :: ts -> Some (create_fap, 7, 8, LP :: ts) (*EP.2 e*)
  | _ :: [END_OF_INPUT] -> failwith "Syntax error"
  | _ -> None


let rec parse_expr ts = parse_binary parse_simple_expr parse_op ts 
and parse_simple_expr ts = match ts with
  | LP :: ts -> let l, ts =  (ex_in_paren ts []) in (*EP.2 e*)
                let e_in_p, t = parse_expr l in
                e_in_p, ts
                
  | INT :: ts -> Ty Int, ts
  | BOOL :: ts -> Ty Bool, ts
  | ICON c :: ts -> Icon c, ts 
  | BCON c :: ts -> Bcon c, ts
  | VAR x  :: ts -> Var x, ts
  | LET :: REC :: ts -> let f,  ts = expect_id ts in (*added*)
                        let     ts = expect LP ts in
                        let x,  ts = expect_id ts in
                        let     ts = expect COL ts in
                        let Ty t1, ts = parse_expr ts in
                        let     ts = expect RP ts in
                        let     ts = expect COL ts in
                        let Ty t2, ts = parse_expr ts in
                        let     ts = expect EQ ts in
                        let e1, ts = parse_expr ts in
                        let     ts = expect IN ts in
                        let e2, ts = parse_expr ts in
                        Letrec (f, x, t1, t2, e1, e2), ts
  | LET    :: ts -> let x,  ts = expect_id ts in
                    let     ts = expect EQ ts in
                    let e1, ts = parse_expr ts in
                    let     ts = expect IN ts in
                    let e2, ts = parse_expr ts in
                    let     ts = expect END_OF_INPUT ts in
                    Let (x, e1, e2), ts
  | IF     :: ts -> let e1, ts = parse_expr ts in
                    let     ts = expect THEN ts in
                    let e2, ts = parse_expr ts in
                    let     ts = expect ELSE ts in
                    let e3, ts = parse_expr ts in
                    If (e1, e2, e3), ts
  | FUN    :: ts -> let    ts = expect LP ts in (*added*)
                    let x, ts = expect_id ts in 
                    let    ts = expect COL ts in
                    let Ty t, ts = parse_expr ts in
                    let    ts = expect RP ts in
                    let    ts = expect ARROW ts in
                    let e, ts = parse_expr ts in
                    Lam (x, t, e), ts
  | _ -> failwith "syntax error"
  
;;

parse_expr (lex "1+2 let;");;

let ex1 = "let rec f (x : int) : int = if x <= 1 then x else x * f (x - 1) in f 5";;
let l1 = lex ex1;;
let p1 = parse_expr l1;;
let c1 = check_ty [] (fst p1)
let e1 = eval [] (fst p1)


let ex2 = "fun (x : int) -> x + 1;"
let l2 = lex ex2
let p2 = parse_expr l2;;
let c2 = check_ty [] (fst p2);;
let e2 = eval [] (fst p2)


let ex3 = "(fun (x : int) -> x + 1) 2;";;
let l3 = lex ex3;;
let p3 = parse_expr l3;;
let c3 = check_ty [] (fst p3);;
let e3 = eval [] (fst p3)
;;
