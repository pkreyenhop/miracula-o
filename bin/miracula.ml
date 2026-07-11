(* ========================================================================== *)
(* 1. TYPE & ENVIRONMENT DEFINITIONS USING MODULES                            *)
(* ========================================================================== *)

module StringMap = Map.Make(String)

type thunk_state =
  | Unevaluated of node * node StringMap.t
  | Evaluating
  | Evaluated of node

and node =
  | Int of int
  | Var of string
  | Lam of string * node
  | Let of (string * node) list * node
  | App of node * node
  | Sub of node * node
  | Add of node * node
  | Mul of node * node
  | IfZero of node * node * node
  | Cons of node * node
  | Nil
  | Range of node * node
  | IfNil of node * node * node
  | MatchError
  | Closure of string * node * node StringMap.t
  | Thunk of thunk_state ref
  | Eq of node * node
  | Ne of node * node
  | Lt of node * node
  | Gt of node * node
  | Le of node * node
  | Ge of node * node
  | Mod of node * node
  | Tuple of node list
  | If of node * node * node
  | Append of node * node
  | Div of node * node
  | Diff of node * node
  | ZFGenerator of parsed_pattern * qualifier list * node * node * node StringMap.t
  | ZF of node * qualifier list
  | Proj of int * node
  | Char of char

and parsed_pattern =
  | PatInt of int
  | PatVar of string
  | PatNil
  | PatCons of parsed_pattern * parsed_pattern
  | PatTuple of parsed_pattern list
  | PatChar of char

and qualifier =
  | Generator of parsed_pattern * node
  | Filter of node

type env = node StringMap.t

exception Blackhole of string
exception RuntimeError of string

(* ========================================================================== *)
(* 2. LEXER IMPLEMENTATION                                                   *)
(* ========================================================================== *)

type token =
  | TOK_LAMBDA | TOK_DOT | TOK_DOTDOT | TOK_ARROW | TOK_ASSIGN
  | TOK_LPAREN | TOK_RPAREN | TOK_LBRACK | TOK_RBRACK | TOK_COMMA | TOK_COLON
  | TOK_SUB | TOK_ADD | TOK_MUL
  | TOK_IFZERO | TOK_THEN | TOK_ELSE
  | TOK_INT of int
  | TOK_VAR of string
  | TOK_EOF
  | TOK_PIPE | TOK_LARROW | TOK_SEMICOLON
  | TOK_EQ | TOK_NE | TOK_LT | TOK_GT | TOK_LE | TOK_GE
  | TOK_MOD | TOK_IF
  | TOK_CHAR of char | TOK_STRING of string | TOK_PP
  | TOK_WHERE | TOK_LBRACE | TOK_RBRACE | TOK_HASH
  | TOK_DIV | TOK_AND | TOK_OR | TOK_DIFF

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_alpha_num c = is_alpha c || is_digit c || c = '_'
let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let tokenize str =
  let size = String.length str in
  let rec loop i acc =
    if i >= size then List.rev (TOK_EOF :: acc)
    else
      let c = String.get str i in
      if is_space c then loop (i + 1) acc
      else if c = '\\' then
        if i + 1 < size && String.get str (i + 1) = '/'
        then loop (i + 2) (TOK_OR :: acc)
        else loop (i + 1) (TOK_LAMBDA :: acc)
      else if c = '.' then
        if i + 1 < size && String.get str (i + 1) = '.'
        then loop (i + 2) (TOK_DOTDOT :: acc)
        else loop (i + 1) (TOK_DOT :: acc)
      else if c = '(' then loop (i + 1) (TOK_LPAREN :: acc)
      else if c = ')' then loop (i + 1) (TOK_RPAREN :: acc)
      else if c = '[' then loop (i + 1) (TOK_LBRACK :: acc)
      else if c = ']' then loop (i + 1) (TOK_RBRACK :: acc)
      else if c = ',' then loop (i + 1) (TOK_COMMA :: acc)
      else if c = ';' then loop (i + 1) (TOK_SEMICOLON :: acc)
      else if c = '|' then
        if i + 1 < size && String.get str (i + 1) = '|'
        then List.rev (TOK_EOF :: acc)
        else loop (i + 1) (TOK_PIPE :: acc)
      else if c = '<' then
        if i + 1 < size && String.get str (i + 1) = '-'
        then loop (i + 2) (TOK_LARROW :: acc)
        else if i + 1 < size && String.get str (i + 1) = '='
        then loop (i + 2) (TOK_LE :: acc)
        else loop (i + 1) (TOK_LT :: acc)
      else if c = '>' then
        if i + 1 < size && String.get str (i + 1) = '='
        then loop (i + 2) (TOK_GE :: acc)
        else loop (i + 1) (TOK_GT :: acc)
      else if c = '=' then
        if i + 1 < size && String.get str (i + 1) = '='
        then loop (i + 2) (TOK_EQ :: acc)
        else loop (i + 1) (TOK_ASSIGN :: acc)
      else if c = '!' then
        if i + 1 < size && String.get str (i + 1) = '='
        then loop (i + 2) (TOK_NE :: acc)
        else (Printf.printf "Lex error: char %c\n" c; loop (i + 1) acc)
      else if c = '~' then
        if i + 1 < size && String.get str (i + 1) = '='
        then loop (i + 2) (TOK_NE :: acc)
        else (Printf.printf "Lex error: char %c\n" c; loop (i + 1) acc)
      else if c = '/' then loop (i + 1) (TOK_DIV :: acc)
      else if c = '&' then loop (i + 1) (TOK_AND :: acc)
      else if c = '*' then loop (i + 1) (TOK_MUL :: acc)
      else if c = ':' then loop (i + 1) (TOK_COLON :: acc)
      else if c = '#' then loop (i + 1) (TOK_HASH :: acc)
      else if c = '+' then
        if i + 1 < size && String.get str (i + 1) = '+'
        then loop (i + 2) (TOK_PP :: acc)
        else loop (i + 1) (TOK_ADD :: acc)
      else if c = '-' then
        if i + 1 < size && String.get str (i + 1) = '>'
        then loop (i + 2) (TOK_ARROW :: acc)
        else if i + 1 < size && String.get str (i + 1) = '-'
        then loop (i + 2) (TOK_DIFF :: acc)
        else loop (i + 1) (TOK_SUB :: acc)
      else if c = '\'' then
        if i + 2 < size && String.get str (i + 1) <> '\\' && String.get str (i + 2) = '\'' then
          loop (i + 3) (TOK_CHAR (String.get str (i + 1)) :: acc)
        else if i + 3 < size && String.get str (i + 1) = '\\' && String.get str (i + 3) = '\'' then
          let esc = String.get str (i + 2) in
          let ch = match esc with
            | 'n' -> '\n'
            | 't' -> '\t'
            | '\'' -> '\''
            | '\\' -> '\\'
            | _ -> esc
          in
          loop (i + 4) (TOK_CHAR ch :: acc)
        else (print_endline "Lex error: invalid char literal"; loop (i + 1) acc)
      else if c = '"' then
        let rec read_str j s =
          if j >= size then (j, s)
          else
            let c' = String.get str j in
            if c' = '"' then (j + 1, s)
            else if c' = '\\' && j + 1 < size then
              let esc = String.get str (j + 1) in
              let ch = match esc with
                | 'n' -> '\n'
                | 't' -> '\t'
                | '"' -> '"'
                | '\\' -> '\\'
                | _ -> esc
              in
              read_str (j + 2) (s ^ String.make 1 ch)
            else
              read_str (j + 1) (s ^ String.make 1 c')
        in
        let (next_j, s) = read_str (i + 1) "" in
        loop next_j (TOK_STRING s :: acc)
      else if is_digit c then
        let rec read_num j s =
          if j < size && is_digit (String.get str j)
          then read_num (j + 1) (s ^ String.make 1 (String.get str j))
          else (j, int_of_string s)
        in
        let (next_j, v) = read_num (i + 1) (String.make 1 c) in
        loop next_j (TOK_INT v :: acc)
      else if is_alpha c || c = '_' then
        let rec read_var j s =
          if j < size && is_alpha_num (String.get str j)
          then read_var (j + 1) (s ^ String.make 1 (String.get str j))
          else (j, s)
        in
        let (next_j, s) = read_var (i + 1) (String.make 1 c) in
        let tok = match s with
          | "ifzero" -> TOK_IFZERO
          | "if"     -> TOK_IF
          | "then"   -> TOK_THEN
          | "else"   -> TOK_ELSE
          | "mod"    -> TOK_MOD
          | "where"  -> TOK_WHERE
          | _        -> TOK_VAR s
        in loop next_j (tok :: acc)
      else (Printf.printf "Lex error: char %c\n" c; loop (i + 1) acc)
  in loop 0 []

(* ========================================================================== *)
(* 3. PARSER MECHANICS                                                       *)
(* ========================================================================== *)

type raw_binding = { fname: string; pats: parsed_pattern list; body: node }
type stmt = ScriptBind of raw_binding | REPLEval of node

let var_counter = ref 0
let new_var_name prefix =
  let c = !var_counter in
  var_counter := c + 1;
  prefix ^ "_" ^ string_of_int c

let rec desugar_equations (eqs : raw_binding list) : node =
  match eqs with
  | [] -> failwith "Empty equation sequence"
  | [ { pats = []; body; _ } ] -> body
  | [ { pats = [PatVar x]; body; _ } ] -> Lam (x, body)
  | _ ->
      let first_binding = List.hd eqs in
      let arity = List.length first_binding.pats in
      if List.exists (fun {pats; _} -> List.length pats <> arity) eqs 
      then failwith "Equations have mismatched parameter arities";
      
      let rec make_param_names n acc =
        if n = 0 then acc else make_param_names (n - 1) (("p" ^ string_of_int (n - 1)) :: acc)
      in
      let param_names = make_param_names arity [] in

      let rec build_decision_tree branches =
        match branches with
        | [] -> MatchError
        | {pats; body; _} :: rest ->
            let rec check_pats p_vars pattern_list tree_body =
              match (p_vars, pattern_list) with
              | ([], []) -> tree_body
              | (p :: p_rest, pat :: pat_rest) ->
                  (match pat with
                   | PatInt target_val ->
                       IfZero (Sub (Var p, Int target_val), check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                   | PatChar target_val ->
                       IfZero (Sub (Eq (Var p, Char target_val), Int 1), check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                   | PatVar binding_name ->
                       let substituted_body = 
                         if binding_name = p then tree_body
                         else App (Lam (binding_name, tree_body), Var p)
                       in check_pats p_rest pat_rest substituted_body
                   | PatTuple tuple_pats ->
                       let elms_vars = List.init (List.length tuple_pats) (fun i -> new_var_name ("t" ^ string_of_int i)) in
                       let inner_body = check_pats (elms_vars @ p_rest) (tuple_pats @ pat_rest) tree_body in
                       let rec wrap_projs vars i body =
                         match vars with
                         | [] -> body
                         | var :: rest_vars -> App (Lam (var, wrap_projs rest_vars (i + 1) body), Proj (i, Var p))
                       in wrap_projs elms_vars 0 inner_body
                   | PatNil ->
                       IfNil (Var p, check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                   | PatCons (head_pat, tail_pat) ->
                       let h_var = new_var_name "h" in
                       let t_var = new_var_name "t" in
                       let failure_branch = build_decision_tree rest in
                       let inner_body = check_pats (h_var :: t_var :: p_rest) (head_pat :: tail_pat :: pat_rest) tree_body in
                       IfNil (Var p, failure_branch,
                              App (Lam (h_var, App (Lam (t_var, inner_body), App (Var "tl", Var p))),
                                   App (Var "hd", Var p))))
              | _ -> failwith "Internal pattern arity violation"
            in check_pats param_names pats body
      in
      let decision_tree = build_decision_tree eqs in
      List.fold_right (fun p acc -> Lam (p, acc)) param_names decision_tree

and parse tokens =
  let toks = ref tokens in
  let peek () = List.hd !toks in
  let consume () = toks := List.tl !toks in
  let peek2 () = match !toks with _ :: t :: _ -> Some t | _ -> None in
  let peek3 () = match !toks with _ :: _ :: t :: _ -> Some t | _ -> None in

  let rec parse_expr () =
    let e = match peek () with
      | TOK_LAMBDA ->
          consume ();
          (match peek () with
           | TOK_VAR x ->
               consume ();
               if peek () <> TOK_DOT then failwith "Expected '.' after lambda variable";
               consume ();
               Lam (x, parse_expr ())
           | _ -> failwith "Expected variable after lambda '\\'")
      | TOK_IFZERO ->
          consume ();
          let cond = parse_expr () in
          if peek () <> TOK_THEN then failwith "Expected 'then'" else consume ();
          let t_branch = parse_expr () in
          if peek () <> TOK_ELSE then failwith "Expected 'else'" else consume ();
          let f_branch = parse_expr () in
          IfZero (cond, t_branch, f_branch)
      | TOK_IF ->
          consume ();
          let cond = parse_expr () in
          if peek () <> TOK_THEN then failwith "Expected 'then'" else consume ();
          let t_branch = parse_expr () in
          if peek () <> TOK_ELSE then failwith "Expected 'else'" else consume ();
          let f_branch = parse_expr () in
          If (cond, t_branch, f_branch)
      | _ -> parse_or ()
    in
    match peek () with
    | TOK_WHERE ->
        consume ();
        if peek () <> TOK_LBRACE then failwith "Expected '{' after 'where'";
        consume ();
        let rec parse_bindings () =
          if peek () = TOK_RBRACE then (consume (); [])
          else
            let b = if is_assignment !toks then
                match peek () with
                | TOK_VAR name ->
                    consume ();
                    let rec collect_patterns acc =
                      if peek () = TOK_ASSIGN then (consume (); List.rev acc)
                      else collect_patterns (parse_pattern () :: acc)
                    in
                    let pats = collect_patterns [] in
                    let expr_body = parse_expr () in
                    { fname = name; pats; body = expr_body }
                | _ -> failwith "Left hand side of local binding must start with an identifier"
              else
                failwith "Expected local binding in where clause"
            in
            let rest = if peek () = TOK_SEMICOLON then (consume (); parse_bindings ())
              else if peek () = TOK_RBRACE then (consume (); [])
              else failwith "Expected ';' or '}' in where bindings"
            in b :: rest
        in
        let bs = parse_bindings () in
        let update_group b m =
          let current = match StringMap.find_opt b.fname m with Some l -> l | None -> [] in
          StringMap.add b.fname (current @ [b]) m
        in
        let grouped = List.fold_left (fun acc b -> update_group b acc) StringMap.empty bs in
        let desugared_bindings = StringMap.fold (fun fname eq_list acc ->
            (fname, desugar_equations eq_list) :: acc
          ) grouped []
        in Let (desugared_bindings, e)
    | _ -> e

  and parse_or () =
    let left = parse_and () in
    match peek () with
    | TOK_OR -> consume (); If (left, Int 1, parse_or ())
    | _ -> left

  and parse_and () =
    let left = parse_cons () in
    match peek () with
    | TOK_AND -> consume (); If (left, parse_and (), Int 0)
    | _ -> left

  and parse_cons () =
    let left = parse_pp () in
    match peek () with
    | TOK_COLON -> consume (); Cons (left, parse_cons ())
    | _ -> left

  and parse_pp () =
    let left = parse_comp () in
    match peek () with
    | TOK_PP -> consume (); Append (left, parse_pp ())
    | TOK_DIFF -> consume (); Diff (left, parse_pp ())
    | _ -> left

  and parse_comp () =
    let left = parse_add_sub () in
    match peek () with
    | TOK_EQ -> consume (); Eq (left, parse_add_sub ())
    | TOK_NE -> consume (); Ne (left, parse_add_sub ())
    | TOK_LT -> consume (); Lt (left, parse_add_sub ())
    | TOK_GT -> consume (); Gt (left, parse_add_sub ())
    | TOK_LE -> consume (); Le (left, parse_add_sub ())
    | TOK_GE -> consume (); Ge (left, parse_add_sub ())
    | _ -> left

  and parse_add_sub () =
    let rec loop left =
      match peek () with
      | TOK_ADD -> consume (); loop (Add (left, parse_mod ()))
      | TOK_SUB -> consume (); loop (Sub (left, parse_mod ()))
      | _ -> left
    in loop (parse_mod ())

  and parse_mod () =
    let rec loop left =
      match peek () with
      | TOK_MOD -> consume (); loop (Mod (left, parse_compose ()))
      | TOK_MUL -> consume (); loop (Mul (left, parse_compose ()))
      | TOK_DIV -> consume (); loop (Div (left, parse_compose ()))
      | _ -> left
    in loop (parse_compose ())

  and parse_compose () =
    let left = parse_app () in
    match peek () with
    | TOK_DOT ->
        consume ();
        let right = parse_compose () in
        let var = new_var_name "cx" in
        Lam (var, App (left, App (right, Var var)))
    | _ -> left

  and parse_app () =
    let rec loop left =
      match peek () with
      | TOK_INT _ | TOK_CHAR _ | TOK_STRING _ | TOK_VAR _ | TOK_LPAREN | TOK_LBRACK ->
          loop (App (left, parse_atom ()))
      | _ -> left
    in loop (parse_atom ())

  and parse_atom () =
    match peek () with
    | TOK_HASH -> consume (); App (Var "length", parse_atom ())
    | TOK_INT n -> consume (); Int n
    | TOK_CHAR c -> consume (); Char c
    | TOK_STRING s ->
        let rec make_list chars =
          match chars with
          | [] -> Nil
          | c :: cs -> Cons (Char c, make_list cs)
        in
        consume ();
        let rec explode str idx acc =
          if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc)
        in
        make_list (explode s (String.length s - 1) [])
    | TOK_VAR x -> consume (); Var x
    | TOK_LPAREN ->
        if peek2 () = Some TOK_COLON then
          if peek3 () = Some TOK_RPAREN then
            (consume (); consume (); consume (); Lam ("x", Lam ("y", Cons (Var "x", Var "y"))))
          else
            (consume (); consume ();
             let e = parse_expr () in
             if peek () <> TOK_RPAREN then failwith "Expected ')'";
             consume ();
             Lam ("x", Cons (Var "x", e)))
        else if peek2 () = Some TOK_ADD then
          if peek3 () = Some TOK_RPAREN then
            (consume (); consume (); consume (); Lam ("x", Lam ("y", Add (Var "x", Var "y"))))
          else
            (consume (); consume ();
             let e = parse_expr () in
             if peek () <> TOK_RPAREN then failwith "Expected ')'";
             consume ();
             Lam ("x", Add (Var "x", e)))
        else if peek2 () = Some TOK_SUB then
          if peek3 () = Some TOK_RPAREN then
            (consume (); consume (); consume (); Lam ("x", Lam ("y", Sub (Var "x", Var "y"))))
          else
            (consume (); consume ();
             let e = parse_expr () in
             if peek () <> TOK_RPAREN then failwith "Expected ')'";
             consume ();
             Lam ("x", Sub (Var "x", e)))
        else
          (consume ();
           let rec parse_tuple_elms acc =
             let e = parse_expr () in
             match peek () with
             | TOK_COMMA -> consume (); parse_tuple_elms (e :: acc)
             | TOK_RPAREN -> consume (); List.rev (e :: acc)
             | _ -> failwith "Expected ',' or ')' inside tuple"
           in
           let first = parse_expr () in
           if peek () = TOK_COMMA then
             (consume (); Tuple (parse_tuple_elms [first]))
           else
             (if peek () <> TOK_RPAREN then failwith "Expected ')'"; consume (); first))
    | TOK_SUB -> consume (); Sub (Int 0, parse_atom ())
    | TOK_LBRACK -> consume (); parse_list_elements ()
    | _ -> failwith "Unexpected token inside atom expression"

  and parse_list_elements () =
    if peek () = TOK_RBRACK then (consume (); Nil)
    else
      let head = parse_expr () in
      if peek () = TOK_PIPE then
        (consume ();
         let has_larrow () =
           let rec check ts =
             match ts with
             | [] -> false
             | TOK_SEMICOLON :: _ -> false
             | TOK_RBRACK :: _ -> false
             | TOK_LARROW :: _ -> true
             | _ :: rest -> check rest
           in check !toks
         in
         let rec parse_qualifiers () =
           let q = if has_larrow () then
               let pat = parse_pattern () in
               if peek () <> TOK_LARROW then failwith "Expected '<-'" else consume ();
               let src = parse_expr () in
               Generator (pat, src)
             else
               Filter (parse_expr ())
           in
           match peek () with
           | TOK_SEMICOLON -> consume (); q :: parse_qualifiers ()
           | TOK_RBRACK -> consume (); [q]
           | _ -> failwith "Expected ';' or ']' in qualifiers"
         in
         let quals = parse_qualifiers () in
         ZF (head, quals))
      else if peek () = TOK_DOTDOT then
        (consume ();
         let tail_expr = parse_expr () in
         if peek () <> TOK_RBRACK then failwith "Expected ']' after range expression";
         consume ();
         Range (head, tail_expr))
      else if peek () = TOK_COMMA then (consume (); Cons (head, parse_list_elements ()))
      else if peek () = TOK_RBRACK then (consume (); Cons (head, Nil))
      else failwith "Expected '|', '..', ',', or ']' in list expression"

  and is_assignment ts =
    let rec check t_list =
      match t_list with
      | [] -> false
      | TOK_SEMICOLON :: _ -> false
      | TOK_RBRACE :: _ -> false
      | TOK_ASSIGN :: _ -> true
      | _ :: rest -> check rest
    in check ts

  and parse_pattern () =
    match peek () with
    | TOK_INT n -> consume (); PatInt n
    | TOK_CHAR c -> consume (); PatChar c
    | TOK_VAR x -> consume (); PatVar x
    | TOK_LBRACK ->
        consume ();
        if peek () = TOK_RBRACK then (consume (); PatNil)
        else failwith "Only empty list pattern '[]' is supported directly"
    | TOK_LPAREN ->
        consume ();
        let rec parse_tuple_pats acc =
          let p = parse_pattern_cons () in
          match peek () with
          | TOK_COMMA -> consume (); parse_tuple_pats (p :: acc)
          | TOK_RPAREN -> consume (); List.rev (p :: acc)
          | _ -> failwith "Expected ',' or ')' inside tuple pattern"
        in
        let first = parse_pattern_cons () in
        if peek () = TOK_COMMA then
          (consume (); PatTuple (parse_tuple_pats [first]))
        else
          (if peek () <> TOK_RPAREN then failwith "Expected ')' in pattern"; consume (); first)
    | _ -> failwith "Malformed pattern in equation left hand side"

  and parse_pattern_cons () =
    let left = parse_pattern () in
    match peek () with
    | TOK_COLON -> consume (); PatCons (left, parse_pattern_cons ())
    | _ -> left
  in

  if is_assignment !toks then
    match peek () with
    | TOK_VAR name ->
        consume ();
        let rec collect_patterns acc =
          if peek () = TOK_ASSIGN then (consume (); List.rev acc)
          else collect_patterns (parse_pattern () :: acc)
        in
        let pats = collect_patterns [] in
        let expr_body = parse_expr () in
        ScriptBind { fname = name; pats; body = expr_body }
    | _ -> failwith "Left hand side of binding must start with an identifier"
  else
    let e = parse_expr () in
    if peek () <> TOK_EOF then failwith "Trailing tokens left unparsed";
    REPLEval e

(* ========================================================================== *)
(* 4. RUNTIME WORKSPACE                                                      *)
(* ========================================================================== *)

let rec match_pattern env pat target_node =
  match (pat, whnf env target_node) with
  | (PatInt n1, Int n2) -> if n1 = n2 then Some StringMap.empty else None
  | (PatChar c1, Char c2) -> if c1 = c2 then Some StringMap.empty else None
  | (PatVar "_", _) -> Some StringMap.empty
  | (PatVar x, v) -> Some (StringMap.singleton x v)
  | (PatNil, Nil) -> Some StringMap.empty
  | (PatCons (p1, p2), Cons (h, t)) ->
      (match (match_pattern env p1 h, match_pattern env p2 t) with
       | (Some m1, Some m2) -> Some (StringMap.union (fun _ _ v2 -> Some v2) m1 m2)
       | _ -> None)
  | (PatTuple pats, Tuple nodes) ->
      if List.length pats = List.length nodes then
        let rec match_list p_list n_list acc =
          match (p_list, n_list) with
          | ([], []) -> Some acc
          | (p :: ps, n :: ns) ->
              (match match_pattern env p n with
               | Some m -> match_list ps ns (StringMap.union (fun _ _ v2 -> Some v2) acc m)
               | _ -> None)
          | _ -> None
        in match_list pats nodes StringMap.empty
      else None
  | _ -> None

and eval_zf env body_expr qualifiers =
  match qualifiers with
  | [] ->
      let needs_thunk n = match n with
        | Int _ | Char _ | Nil | Thunk _ | Closure _ | Lam _ | MatchError -> false
        | _ -> true
      in
      let h = if needs_thunk body_expr then Thunk (ref (Unevaluated (body_expr, env))) else body_expr in
      Cons (h, Nil)
  | Filter cond :: rest ->
      let cond' = Thunk (ref (Unevaluated (cond, env))) in
      If (cond', eval_zf env body_expr rest, Nil)
  | Generator (pat, src) :: rest ->
      ZFGenerator (pat, rest, src, body_expr, env)

and get_string_value env target_node =
  let rec collect current acc =
    match whnf env current with
    | Nil ->
        let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
        implode (List.rev acc)
    | Cons (h, t) ->
        (match whnf env h with
         | Char c -> collect t (c :: acc)
         | _ -> raise (RuntimeError "Expected char in string"))
    | _ -> raise (RuntimeError "Expected string")
  in collect target_node []

and make_string_node s =
  let rec make chars =
    match chars with
    | [] -> Nil
    | c :: cs -> Cons (Char c, make cs)
  in
  let rec explode str idx acc =
    if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc)
  in
  make (explode s (String.length s - 1) [])

and read_file_content filename =
  try
    let ic = open_in filename in
    let rec read_all acc =
      try
        let line = input_line ic in
        read_all ((line ^ "\n") :: acc)
      with End_of_file ->
        close_in ic;
        String.concat "" (List.rev acc)
    in read_all []
  with _ -> raise (RuntimeError ("Failed to read file: " ^ filename))

and whnf (env : env) (n : node) : node =
  match n with
  | Int n -> Int n
  | Char c -> Char c
  | Lam (x, body) -> Closure (x, body, env)
  | Closure (x, body, closure_env) -> Closure (x, body, closure_env)
  | Let (bindings, body) ->
      let dummy_env = StringMap.empty in
      let env' = List.fold_left (fun acc (x_i, e_i) ->
          let r = ref (Unevaluated (e_i, dummy_env)) in
          StringMap.add x_i (Thunk r) acc
        ) env bindings
      in
      List.iter (fun (x_i, e_i) ->
          match StringMap.find_opt x_i env' with
          | Some (Thunk r) -> r := Unevaluated (e_i, env')
          | _ -> ()
        ) bindings;
      whnf env' body
  | Cons (h, t) ->
      let needs_thunk node_to_check = match node_to_check with
        | Int _ | Char _ | Nil | Thunk _ | Closure _ | Lam _ | Cons _ | MatchError -> false
        | _ -> true
      in
      let h' = if needs_thunk h then Thunk (ref (Unevaluated (h, env))) else h in
      let t' = if needs_thunk t then Thunk (ref (Unevaluated (t, env))) else t in
      Cons (h', t')
  | Nil -> Nil
  | Eq (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> if n1 = n2 then Int 1 else Int 0
       | (Char c1, Char c2) -> if c1 = c2 then Int 1 else Int 0
       | (Nil, Nil) -> Int 1
       | (Cons (h1, t1), Cons (h2, t2)) ->
           (match whnf env (Eq (h1, h2)) with
            | Int 1 -> whnf env (Eq (t1, t2))
            | _ -> Int 0)
       | (Nil, Cons _) -> Int 0
       | (Cons _, Nil) -> Int 0
       | (Tuple elms1, Tuple elms2) ->
           if List.length elms1 = List.length elms2 then
             let rec check_elms l1 l2 =
               match (l1, l2) with
               | ([], []) -> Int 1
               | (x :: xs, y :: ys) ->
                   (match whnf env (Eq (x, y)) with
                    | Int 1 -> check_elms xs ys
                    | _ -> Int 0)
               | _ -> Int 0
             in check_elms elms1 elms2
           else Int 0
       | (other1, other2) -> raise (RuntimeError ("Equality expects integers, characters, lists or tuples, got: " ^ print_node env other1 ^ " and " ^ print_node env other2)))
  | Ne (e1, e2) ->
      (match whnf env (Eq (e1, e2)) with
       | Int 1 -> Int 0
       | Int 0 -> Int 1
       | _ -> raise (RuntimeError "Inequality expects boolean result from equality"))
  | Lt (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> if n1 < n2 then Int 1 else Int 0
       | _ -> raise (RuntimeError "Less-than expects integers"))
  | Gt (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> if n1 > n2 then Int 1 else Int 0
       | _ -> raise (RuntimeError "Greater-than expects integers"))
  | Le (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> if n1 <= n2 then Int 1 else Int 0
       | _ -> raise (RuntimeError "Less-than-or-equal expects integers"))
  | Ge (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> if n1 >= n2 then Int 1 else Int 0
       | _ -> raise (RuntimeError "Greater-than-or-equal expects integers"))
  | Mod (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> Int (n1 mod n2)
       | _ -> raise (RuntimeError "Modulo expects integers"))
  | Tuple elms ->
      let needs_thunk node_to_check = match node_to_check with
        | Int _ | Char _ | Nil | Thunk _ | Closure _ | Lam _ | Cons _ | Tuple _ | MatchError -> false
        | _ -> true
      in
      let elms' = List.map (fun e -> if needs_thunk e then Thunk (ref (Unevaluated (e, env))) else e) elms in
      Tuple elms'
  | If (cond, t_branch, f_branch) ->
      (match whnf env cond with
       | Int 0 -> whnf env f_branch
       | Int _ -> whnf env t_branch
       | other ->
           let test_name = match StringMap.find_opt "name" env with
             | Some n -> print_node env (whnf env n)
             | None -> "<unknown>"
           in
           let cond_ast = match StringMap.find_opt "cond" env with
             | Some (Thunk r) ->
                 (match !r with
                  | Unevaluated (expr, _) -> print_node env expr
                  | Evaluated n' -> print_node env n'
                  | Evaluating -> "<evaluating>")
             | Some n' -> print_node env n'
             | None -> "<none>"
           in
           raise (RuntimeError ("In test '" ^ test_name ^ "': If condition must be an integer, got: " ^ print_node env other ^ " for condition expression AST: " ^ cond_ast)))
  | Append (e1, e2) ->
      (match whnf env e1 with
       | Nil -> whnf env e2
       | Cons (h, t) ->
           let t' = Thunk (ref (Unevaluated (Append (t, e2), env))) in
           Cons (h, t')
       | _ -> raise (RuntimeError "Append expects lists"))
  | ZF (body_expr, qualifiers) ->
      whnf env (eval_zf env body_expr qualifiers)
  | ZFGenerator (pat, rest, current_list, body_expr, zf_env) ->
      (match whnf zf_env current_list with
       | Nil -> Nil
       | Cons (h, t) ->
           let match_res = match_pattern zf_env pat h in
           let next_gen = ZFGenerator (pat, rest, t, body_expr, zf_env) in
           (match match_res with
            | Some bindings ->
                let extended_env = StringMap.fold (fun k v acc -> StringMap.add k v acc) bindings zf_env in
                let first_list = eval_zf extended_env body_expr rest in
                whnf env (Append (first_list, next_gen))
            | None -> whnf env next_gen)
       | _ -> raise (RuntimeError "Generator source must be a list"))
  | Var x ->
      if x = "hd" || x = "tl" || x = "show" || x = "read" || x = "lines" || x = "numval" || x = "length" then Var x
      else
        (match StringMap.find_opt x env with
         | Some (Thunk r) ->
             (match !r with
              | Evaluated n' -> n'
              | Evaluating  -> raise (Blackhole ("Infinite loop on identifier: " ^ x))
              | Unevaluated (expr, saved_env) ->
                  r := Evaluating;
                  let result = whnf saved_env expr in
                  r := Evaluated result;
                  result)
         | Some explicit_node -> whnf env explicit_node
         | None -> 
             let keys = StringMap.fold (fun k _ acc -> k :: acc) env [] in
             raise (RuntimeError ("Unbound variable: " ^ x ^ ", environment keys: " ^ String.concat ", " keys)))
  | App (e1, e2) ->
      (match whnf env e1 with
       | Var "hd" ->
           (match whnf env e2 with
            | Cons (h, _) -> whnf env h
            | Nil -> raise (RuntimeError "hd applied to empty list")
            | _ -> raise (RuntimeError "hd expects a list"))
       | Var "tl" ->
           (match whnf env e2 with
            | Cons (_, t) -> whnf env t
            | Nil -> raise (RuntimeError "tl applied to empty list")
            | _ -> raise (RuntimeError "tl expects a list"))
       | Var "read" ->
           let filename = get_string_value env e2 in
           let content = read_file_content filename in
           make_string_node content
       | Var "lines" ->
           let content = get_string_value env e2 in
           let split_lines s =
             let rec fields current acc i =
               if i >= String.length s then List.rev (current :: acc)
               else if String.get s i = '\n' then fields "" (current :: acc) (i + 1)
               else fields (current ^ String.make 1 (String.get s i)) acc (i + 1)
             in
             let res = fields "" [] 0 in
             match List.rev res with
             | "" :: rest -> List.rev rest
             | _ -> res
           in
           let str_list = split_lines content in
           let rec make_node_list list_strings =
             match list_strings with
             | [] -> Nil
             | str :: strs -> Cons (make_string_node str, make_node_list strs)
           in make_node_list str_list
       | Var "numval" ->
           let s = get_string_value env e2 in
           let rec filter_space s i acc =
             if i >= String.length s then acc
             else if is_space (String.get s i) then filter_space s (i + 1) acc
             else filter_space s (i + 1) (acc ^ String.make 1 (String.get s i))
           in
           let s_trimmed = filter_space s 0 "" in
           (try Int (int_of_string s_trimmed) with _ -> raise (RuntimeError ("numval: invalid integer: " ^ s)))
       | Var "show" ->
           let evaluated_node = whnf env e2 in
           let s = print_node env evaluated_node in
           make_string_node s
       | Var "length" ->
           let rec len list_node =
             match whnf env list_node with
             | Nil -> 0
             | Cons (_, t) -> 1 + len t
             | _ -> raise (RuntimeError "length expects a list")
           in Int (len e2)
       | Closure (x, body, closure_env) ->
           let shared_thunk = Thunk (ref (Unevaluated (e2, env))) in
           let extended_env = StringMap.add x shared_thunk closure_env in
           whnf extended_env body
       | Lam (x, body) ->
           let shared_thunk = Thunk (ref (Unevaluated (e2, env))) in
           let extended_env = StringMap.add x shared_thunk env in
           whnf extended_env body
       | _ -> raise (RuntimeError "Non-functional application"))
  | Sub (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> Int (n1 - n2)
       | _ -> raise (RuntimeError "Subtraction expects integers"))
  | Add (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> Int (n1 + n2)
       | _ -> raise (RuntimeError "Addition expects integers"))
  | Mul (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) -> Int (n1 * n2)
       | _ -> raise (RuntimeError "Multiplication expects integers"))
  | Div (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) ->
           if n2 = 0 then raise (RuntimeError "Division by zero")
           else Int (n1 / n2)
       | _ -> raise (RuntimeError "Division expects integers"))
  | Diff (e1, e2) ->
      let xs = whnf env e1 in
      let ys = whnf env e2 in
      let rec remove_one x list_node =
        match whnf env list_node with
        | Nil -> Nil
        | Cons (h, t) ->
            (match whnf env (Eq (x, h)) with
             | Int 1 -> t
             | _ -> Cons (h, remove_one x t))
        | _ -> raise (RuntimeError "-- expects lists")
      in
      let rec diff list_xs list_ys =
        match list_ys with
        | Nil -> list_xs
        | Cons (y, ys') ->
            let y_eval = whnf env y in
            let xs' = remove_one y_eval list_xs in
            diff xs' (whnf env ys')
        | _ -> raise (RuntimeError "-- expects lists")
      in diff xs ys
  | IfZero (cond, t_branch, f_branch) ->
      (match whnf env cond with
       | Int 0 -> whnf env t_branch
       | Int _ -> whnf env t_branch
       | _ -> raise (RuntimeError "Condition must resolve to an integer"))
  | IfNil (cond, t_branch, f_branch) ->
      (match whnf env cond with
       | Nil -> whnf env t_branch
       | Cons _ -> whnf env f_branch
       | _ -> raise (RuntimeError "Condition must resolve to a list"))
  | Range (e1, e2) ->
      (match (whnf env e1, whnf env e2) with
       | (Int n1, Int n2) ->
           if n1 > n2 then Nil
           else Cons (Int n1, Thunk (ref (Unevaluated (Range (Int (n1 + 1), e2), env))))
       | _ -> raise (RuntimeError "Range bounds must evaluate to integers"))
  | MatchError -> raise (RuntimeError "Pattern matching exhausted")
  | Proj (i, tpl) ->
      (match whnf env tpl with
       | Tuple elms -> whnf env (List.nth elms i)
       | _ -> raise (RuntimeError "Proj expects a tuple"))
  | Thunk r ->
      (match !r with
       | Evaluated n' -> n'
       | Evaluating  -> raise (Blackhole "Infinite loop inside generic thunk node")
       | Unevaluated (expr, saved_env) ->
           r := Evaluating;
           let result = whnf saved_env expr in
           r := Evaluated result;
           result)

and print_node env node =
  match node with
  | Int n -> string_of_int n
  | Lam (x, _) -> "\\" ^ x ^ ". <closure>"
  | Closure (x, _, _) -> "\\" ^ x ^ ". <closure>"
  | Let _ -> "<let>"
  | Var x -> x
  | App (e1, e2) -> "(" ^ print_node env e1 ^ " " ^ print_node env e2 ^ ")"
  | Sub (e1, e2) -> "(" ^ print_node env e1 ^ " - " ^ print_node env e2 ^ ")"
  | Add (e1, e2) -> "(" ^ print_node env e1 ^ " + " ^ print_node env e2 ^ ")"
  | Mul (e1, e2) -> "(" ^ print_node env e1 ^ " * " ^ print_node env e2 ^ ")"
  | Div (e1, e2) -> "(" ^ print_node env e1 ^ " / " ^ print_node env e2 ^ ")"
  | Diff (e1, e2) -> "(" ^ print_node env e1 ^ " -- " ^ print_node env e2 ^ ")"
  | Eq (e1, e2) -> "(" ^ print_node env e1 ^ " == " ^ print_node env e2 ^ ")"
  | Ne (e1, e2) -> "(" ^ print_node env e1 ^ " != " ^ print_node env e2 ^ ")"
  | Lt (e1, e2) -> "(" ^ print_node env e1 ^ " < " ^ print_node env e2 ^ ")"
  | Gt (e1, e2) -> "(" ^ print_node env e1 ^ " > " ^ print_node env e2 ^ ")"
  | Le (e1, e2) -> "(" ^ print_node env e1 ^ " <= " ^ print_node env e2 ^ ")"
  | Ge (e1, e2) -> "(" ^ print_node env e1 ^ " >= " ^ print_node env e2 ^ ")"
  | Mod (e1, e2) -> "(" ^ print_node env e1 ^ " mod " ^ print_node env e2 ^ ")"
  | Tuple elms -> "(" ^ String.concat "," (List.map (fun e -> print_node env (whnf env e)) elms) ^ ")"
  | Proj (i, e) -> "Proj(" ^ string_of_int i ^ ", " ^ print_node env e ^ ")"
  | IfZero _ -> "<conditional>"
  | If _ -> "<conditional>"
  | IfNil _ -> "<conditional-nil>"
  | Append _ -> "<append>"
  | ZF _ -> "<zf-comprehension>"
  | ZFGenerator _ -> "<zf-generator>"
  | MatchError -> "<match-error>"
  | Thunk _ -> "<thunk>"
  | Range (e1, e2) -> "[" ^ print_node env e1 ^ ".." ^ print_node env e2 ^ "]"
  | Char c ->
      let escape ch = match ch with
        | '\n' -> "\\n"
        | '\t' -> "\\t"
        | '\'' -> "\\'"
        | '\\' -> "\\\\"
        | _ -> String.make 1 ch
      in "'" ^ escape c ^ "'"
  | Nil -> "[]"
  | Cons _ ->
      let rec check_string current acc =
        match whnf env current with
        | Nil ->
            let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
            Some (implode (List.rev acc))
        | Cons (h, t) ->
            (match whnf env h with
             | Char c -> check_string t (c :: acc)
             | _ -> None)
        | _ -> None
      in
      match check_string node [] with
      | Some "" -> "[]"
      | Some s ->
          let escape ch = match ch with
            | '\n' -> "\\n"
            | '\t' -> "\\t"
            | '"' -> "\\\""
            | '\\' -> "\\\\"
            | _ -> String.make 1 ch
          in
          let rec translate str idx acc =
            if idx >= String.length str then acc
            else translate str (idx + 1) (acc ^ escape (String.get str idx))
          in "\"" ^ translate s 0 "" ^ "\""
      | None ->
          let rec collect elements current =
            match whnf env current with
            | Cons (h, t) -> collect (print_node env (whnf env h) :: elements) t
            | Nil -> List.rev elements
            | rest -> List.rev (print_node env (whnf env rest) :: elements)
          in "[" ^ String.concat "," (collect [] node) ^ "]"

(* ========================================================================== *)
(* 5. DESUGARER LOGIC & FILE LOADER                                          *)
(* ========================================================================== *)

let print_ast node =
  let rec run n = match n with
    | Int n -> "Int " ^ string_of_int n
    | Char c -> "Char '" ^ String.make 1 c ^ "'"
    | Var x -> "Var " ^ x
    | Lam (x, body) -> "Lam (" ^ x ^ ", " ^ run body ^ ")"
    | Closure (x, body, _) -> "Closure (" ^ x ^ ", " ^ run body ^ ")"
    | Let (bindings, body) ->
        let binds = String.concat "," (List.map (fun (x, e) -> x ^ "=" ^ run e) bindings) in
        "Let ([" ^ binds ^ "], " ^ run body ^ ")"
    | App (e1, e2) -> "App (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Sub (e1, e2) -> "Sub (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Add (e1, e2) -> "Add (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Mul (e1, e2) -> "Mul (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Div (e1, e2) -> "Div (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Diff (e1, e2) -> "Diff (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | IfZero (c, t, f) -> "IfZero (" ^ run c ^ ", " ^ run t ^ ", " ^ run f ^ ")"
    | IfNil (c, t, f) -> "IfNil (" ^ run c ^ ", " ^ run t ^ ", " ^ run f ^ ")"
    | MatchError -> "MatchError"
    | Nil -> "Nil"
    | Cons (h, t) -> "Cons (" ^ run h ^ ", " ^ run t ^ ")"
    | Range (e1, e2) -> "Range (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Thunk _ -> "Thunk"
    | Eq (e1, e2) -> "Eq (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Ne (e1, e2) -> "Ne (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Lt (e1, e2) -> "Lt (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Gt (e1, e2) -> "Gt (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Le (e1, e2) -> "Le (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Ge (e1, e2) -> "Ge (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Mod (e1, e2) -> "Mod (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | Tuple elms -> "Tuple [" ^ String.concat "," (List.map run elms) ^ "]"
    | If (c, t, f) -> "If (" ^ run c ^ ", " ^ run t ^ ", " ^ run f ^ ")"
    | Append (e1, e2) -> "Append (" ^ run e1 ^ ", " ^ run e2 ^ ")"
    | ZF (body, _) -> "ZF (" ^ run body ^ ")"
    | ZFGenerator _ -> "ZFGenerator"
    | Proj (i, e) -> "Proj (" ^ string_of_int i ^ ", " ^ run e ^ ")"
  in run node

let rec load_script_file filename env =
  let file_exists name = try let ins = open_in name in close_in ins; true with _ -> false in
  let count_indent s =
    let rec count chars n = match chars with
      | [] -> n
      | ' ' :: cs -> count cs (n + 1)
      | '\t' :: cs -> count cs (n + 4)
      | _ -> n
    in
    let rec explode str idx acc = if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc) in
    count (explode s (String.length s - 1) []) 0
  in
  let rec has_where ts = match ts with TOK_WHERE :: _ -> true | _ :: rest -> has_where rest | [] -> false in
  let apply_layout (lines : (int * token list) list) : token list =
    let rec token_depth_delta ts = match ts with
      | TOK_LPAREN :: rest -> 1 + token_depth_delta rest
      | TOK_RPAREN :: rest -> -1 + token_depth_delta rest
      | TOK_LBRACK :: rest -> 1 + token_depth_delta rest
      | TOK_RBRACK :: rest -> -1 + token_depth_delta rest
      | _ :: rest -> token_depth_delta rest
      | [] -> 0
    in
    let rec loop stream stack acc expect_layout depth =
      match stream with
      | [] ->
          let closes = List.map (fun _ -> TOK_RBRACE) (List.tl stack) in
          List.rev acc @ closes @ [TOK_EOF]
      | (indent, line_toks) :: rest ->
          let (stack', acc', expect_layout', just_pushed) =
            if expect_layout && depth = 0 then
              let parent_layout = List.hd stack in
              if indent > parent_layout then (indent :: stack, TOK_LBRACE :: acc, false, true)
              else (stack, acc, false, false)
            else (stack, acc, false, false)
          in
          let rec close_layouts s closed_acc =
            if depth = 0 then match s with
              | [] -> ([], closed_acc)
              | [0] -> ([0], closed_acc)
              | top :: under ->
                  if indent < top then close_layouts under (TOK_RBRACE :: closed_acc)
                  else (s, closed_acc)
            else (s, closed_acc)
          in
          let (stack'', close_toks) = close_layouts stack' [] in
          let acc'' = close_toks @ acc' in
          let current_layout = List.hd stack'' in
          let acc''' =
            if depth = 0 && indent = current_layout && acc'' <> [] && not just_pushed
            then TOK_SEMICOLON :: acc'' else acc''
          in
          let next_expect_layout = if depth = 0 then has_where line_toks else false in
          let new_acc = List.rev line_toks @ acc''' in
          let delta = token_depth_delta line_toks in
          let new_depth = max 0 (depth + delta) in
          loop rest stack'' new_acc next_expect_layout new_depth
    in loop lines [0] [] false 0
  in
  let split_tokens tokens =
    let rec loop stream current acc depth =
      match stream with
      | [] ->
          if current = [] then List.rev acc
          else List.rev (List.rev (TOK_EOF :: current) :: acc)
      | t :: ts ->
          if t = TOK_EOF then loop ts current acc depth
          else
            let new_depth = match t with
              | TOK_LBRACE | TOK_LPAREN | TOK_LBRACK -> depth + 1
              | TOK_RBRACE | TOK_RPAREN | TOK_RBRACK -> depth - 1
              | _ -> depth
            in
            if t = TOK_SEMICOLON && depth = 0 then
              let segment = List.rev (TOK_EOF :: current) in
              loop ts [] (segment :: acc) depth
            else
              loop ts (t :: current) acc new_depth
    in loop tokens [] [] 0
  in

  if not (file_exists filename) then (
    if filename = "stdenv.m" then print_endline "Standard environment file 'stdenv.m' not found. Skipping."
    else Printf.printf "Script file '%s' not found. Starting with empty space.\n" filename;
    env
  ) else
    let ic = open_in filename in
    let rec read_lines lines =
      try
        let line = input_line ic in
        let rec filter_cr str i acc =
          if i >= String.length str then acc
          else if String.get str i = '\r' then filter_cr str (i + 1) acc
          else filter_cr str (i + 1) (acc ^ String.make 1 (String.get str i))
        in
        let l = filter_cr line 0 "" in
        let rec is_empty str idx =
          if idx >= String.length str then true
          else if is_space (String.get str idx) then is_empty str (idx + 1)
          else false
        in
        if is_empty l 0 || (String.length l >= 2 && String.sub l 0 2 = "||")
        then read_lines lines
        else read_lines (line :: lines)
      with End_of_file -> close_in ic; List.rev lines
    in
    let raw_lines = read_lines [] in
    let token_to_string t = match t with
      | TOK_LAMBDA -> "\\" | TOK_DOT -> "." | TOK_DOTDOT -> ".." | TOK_ARROW -> "->" | TOK_ASSIGN -> "="
      | TOK_LPAREN -> "(" | TOK_RPAREN -> ")" | TOK_LBRACK -> "[" | TOK_RBRACK -> "]" | TOK_COMMA -> ","
      | TOK_COLON -> ":" | TOK_SUB -> "-" | TOK_ADD -> "+" | TOK_MUL -> "*" | TOK_DIV -> "/"
      | TOK_IFZERO -> "ifzero" | TOK_THEN -> "then" | TOK_ELSE -> "else" | TOK_INT n -> string_of_int n
      | TOK_VAR s -> s | TOK_EOF -> "<EOF>" | TOK_PIPE -> "|" | TOK_LARROW -> "<-" | TOK_SEMICOLON -> ";"
      | TOK_EQ -> "==" | TOK_NE -> "~=" | TOK_LT -> "<" | TOK_GT -> ">" | TOK_LE -> "<=" | TOK_GE -> ">="
      | TOK_MOD -> "mod" | TOK_IF -> "if" | TOK_CHAR c -> "'" ^ String.make 1 c ^ "'" | TOK_STRING s -> "\"" ^ s ^ "\""
      | TOK_PP -> "++" | TOK_WHERE -> "where" | TOK_LBRACE -> "{" | TOK_RBRACE -> "}" | TOK_HASH -> "#"
      | TOK_AND -> "&" | TOK_OR -> "\\/" | TOK_DIFF -> "--"
    in
    let rec wrap_where_on_line stream = match stream with
      | [] -> []
      | TOK_WHERE :: ts -> if ts = [] then [TOK_WHERE] else TOK_WHERE :: TOK_LBRACE :: wrap_where_on_line ts @ [TOK_RBRACE]
      | t :: ts -> t :: wrap_where_on_line ts
    in
    let parsed_lines = List.map (fun line ->
        let indent = count_indent line in
        let rec explode str idx acc = if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc) in
        let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
        let trimmed = implode (List.filter (fun c -> c <> '\r' && c <> '\n') (explode line (String.length line - 1) [])) in
        let rec drop n chars = if n <= 0 then chars else match chars with [] -> [] | _::cs -> drop (n - 1) cs in
        let line_content = implode (drop indent (explode trimmed (String.length trimmed - 1) [])) in
        let line_tokens = List.filter (fun t -> t <> TOK_EOF) (tokenize line_content) in
        (indent, wrap_where_on_line line_tokens)
      ) raw_lines
    in
    let parsed_lines' = List.filter (fun (_, ts) -> ts <> []) parsed_lines in
    let file_tokens = apply_layout parsed_lines' in
    let segments = split_tokens file_tokens in
    let process_segment segment =
      try match parse segment with ScriptBind b -> b | _ -> failwith "Invalid expression structure in script file"
      with ex ->
        Printf.printf "Parse error in segment:\n%s\n" (String.concat " " (List.map token_to_string segment));
        raise ex
    in
    let bindings = List.map process_segment segments in
    let update_group b m =
      let current = match StringMap.find_opt b.fname m with Some l -> l | None -> [] in
      StringMap.add b.fname (current @ [b]) m
    in
    let grouped = List.fold_left (fun acc b -> update_group b acc) StringMap.empty bindings in
    StringMap.fold (fun fname eq_list acc_env ->
        StringMap.add fname (desugar_equations eq_list) acc_env
      ) grouped env

(* ========================================================================== *)
(* 6. REPL ENGINE WITH IN-TERMINAL UNBUFFERED KEY READS                       *)
(* ========================================================================== *)

type key =
  | KeyChar of char | KeyEnter | KeyBackspace | KeyDelete | KeyUp | KeyDown | KeyLeft | KeyRight
  | KeyHome | KeyEnd | KeyCtrlC | KeyCtrlD | KeyCtrlL | KeyCtrlK | KeyUnknown of string

let read_key () =
  try
    match input_char stdin with
    | '\027' ->
        (match input_char stdin with
         | '[' ->
             (match input_char stdin with
              | 'A' -> Some KeyUp | 'B' -> Some KeyDown | 'C' -> Some KeyRight | 'D' -> Some KeyLeft
              | 'H' -> Some KeyHome | 'F' -> Some KeyEnd
              | '1' ->
                  (match input_char stdin with
                   | '~' -> Some KeyHome | _ -> Some (KeyUnknown "esc[1...")
                   | exception End_of_file -> None)
              | '3' ->
                  (match input_char stdin with
                   | '~' -> Some KeyDelete | _ -> Some (KeyUnknown "esc[3...")
                   | exception End_of_file -> None)
              | '4' -> Some KeyEnd | '7' -> Some KeyHome | '8' -> Some KeyEnd
              | c -> Some (KeyUnknown ("esc[" ^ String.make 1 c))
              | exception End_of_file -> None)
         | 'O' ->
             (match input_char stdin with
              | 'H' -> Some KeyHome | 'F' -> Some KeyEnd
              | c -> Some (KeyUnknown ("escO" ^ String.make 1 c))
              | exception End_of_file -> None)
         | c -> Some (KeyUnknown ("esc" ^ String.make 1 c))
         | exception End_of_file -> None)
    | '\n' -> Some KeyEnter | '\r' -> Some KeyEnter
    | '\003' -> Some KeyCtrlC | '\004' -> Some KeyCtrlD | '\012' -> Some KeyCtrlL | '\011' -> Some KeyCtrlK
    | '\127' -> Some KeyBackspace | '\008' -> Some KeyBackspace | '\001' -> Some KeyHome | '\005' -> Some KeyEnd
    | c -> Some (KeyChar c)
  with End_of_file -> None

let redraw prompt left right =
  let full_line = (List.rev left) @ right in
  let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
  let left_str = implode (List.rev left) in
  Printf.printf "\r\027[K%s%s" prompt (implode full_line);
  Printf.printf "\r%s%s" prompt left_str;
  flush stdout

let rec read_line_loop prompt history =
  let rec loop left right hist_idx draft =
    match read_key () with
    | None -> None
    | Some KeyEnter ->
        let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
        let line = implode ((List.rev left) @ right) in
        print_endline ""; flush stdout; Some line
    | Some KeyCtrlC -> print_endline "^C"; flush stdout; Some ""
    | Some KeyCtrlD ->
        if left = [] && right = [] then (print_endline ""; flush stdout; None)
        else
          let new_right = if right = [] then [] else List.tl right in
          redraw prompt left new_right; loop left new_right hist_idx draft
    | Some KeyCtrlL -> Printf.printf "\027[2J\027[H"; redraw prompt left right; loop left right hist_idx draft
    | Some KeyCtrlK -> let new_right = [] in redraw prompt left new_right; loop left new_right hist_idx draft
    | Some KeyBackspace ->
        if left = [] then loop left right hist_idx draft
        else let new_left = List.tl left in redraw prompt new_left right; loop new_left right hist_idx draft
    | Some KeyDelete ->
        if right = [] then loop left right hist_idx draft
        else let new_right = List.tl right in redraw prompt left new_right; loop left new_right hist_idx draft
    | Some KeyLeft ->
        if left = [] then loop left right hist_idx draft
        else
          let c = List.hd left in
          let new_left = List.tl left in
          let new_right = c :: right in
          redraw prompt new_left new_right; loop new_left new_right hist_idx draft
    | Some KeyRight ->
        if right = [] then loop left right hist_idx draft
        else
          let c = List.hd right in
          let new_right = List.tl right in
          let new_left = c :: left in
          redraw prompt new_left new_right; loop new_left new_right hist_idx draft
    | Some KeyHome ->
        let new_right = (List.rev left) @ right in
        let new_left = [] in
        redraw prompt new_left new_right; loop new_left new_right hist_idx draft
    | Some KeyEnd ->
        let new_left = (List.rev right) @ left in
        let new_right = [] in
        redraw prompt new_left new_right; loop new_left new_right hist_idx draft
    | Some KeyUp ->
        let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
        let current_str = implode ((List.rev left) @ right) in
        let new_draft = if hist_idx = -1 then current_str else draft in
        let next_idx = hist_idx + 1 in
        if next_idx < List.length history then
          let hist_item = List.nth history next_idx in
          let rec explode str idx acc = if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc) in
          let new_left = List.rev (explode hist_item (String.length hist_item - 1) []) in
          let new_right = [] in
          redraw prompt new_left new_right; loop new_left new_right next_idx new_draft
        else loop left right hist_idx draft
    | Some KeyDown ->
        if hist_idx = -1 then loop left right hist_idx draft
        else if hist_idx = 0 then
          let rec explode str idx acc = if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc) in
          let new_left = List.rev (explode draft (String.length draft - 1) []) in
          let new_right = [] in
          redraw prompt new_left new_right; loop new_left new_right (-1) ""
        else
          let next_idx = hist_idx - 1 in
          let hist_item = List.nth history next_idx in
          let rec explode str idx acc = if idx < 0 then acc else explode str (idx - 1) (String.get str idx :: acc) in
          let new_left = List.rev (explode hist_item (String.length hist_item - 1) []) in
          let new_right = [] in
          redraw prompt new_left new_right; loop new_left new_right next_idx draft
    | Some (KeyChar c) ->
        let new_left = c :: left in
        redraw prompt new_left right; loop new_left right hist_idx draft
    | Some (KeyUnknown _) -> loop left right hist_idx draft
  in loop [] [] (-1) ""

let get_is_tty () = Sys.command "test -t 0 2>/dev/null" = 0

let read_line prompt history =
  let is_tty = get_is_tty () in
  if not is_tty then (
    print_string prompt; flush stdout;
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> None
    | Some line ->
        let rec filter_nl str i acc =
          if i >= String.length str then acc
          else if String.get str i = '\n' || String.get str i = '\r' then filter_nl str (i + 1) acc
          else filter_nl str (i + 1) (acc ^ String.make 1 (String.get str i))
        in Some (filter_nl line 0 "")
  ) else (
    print_string prompt; flush stdout;
    let _ = Sys.command "stty raw -echo" in
    let res = try read_line_loop prompt history with exn -> let _ = Sys.command "stty -raw echo" in raise exn in
    let _ = Sys.command "stty -raw echo" in
    res
  )

let add_history line history =
  if line = "" then history
  else match history with [] -> [line] | h :: _ -> if h = line then history else line :: history

let rec repl env history script_file =
  match read_line "miranda> " history with
  | None -> print_endline "Goodbye."
  | Some line ->
      let rec filter_nl str i acc =
        if i >= String.length str then acc
        else if String.get str i = '\n' || String.get str i = '\r' then filter_nl str (i + 1) acc
        else filter_nl str (i + 1) (acc ^ String.make 1 (String.get str i))
      in
      let line_trimmed = filter_nl line 0 "" in
      let rec is_empty str idx =
        if idx >= String.length str then true
        else if is_space (String.get str idx) then is_empty str (idx + 1)
        else false
      in
      if line_trimmed = "/q" || line_trimmed = "exit" || line_trimmed = "quit" then print_endline "Goodbye."
      else if line_trimmed = "/e" then (
        Printf.printf "Opening vi %s ...\n" script_file; flush stdout;
        let _ = Sys.command ("vi " ^ script_file) in
        Printf.printf "Reloading environment profiles from %s...\n" script_file;
        let env_with_std = load_script_file "stdenv.m" StringMap.empty in
        let reloaded_env = load_script_file script_file env_with_std in
        repl reloaded_env history script_file
      ) else if is_empty line_trimmed 0 then repl env history script_file
      else
        let updated_history = add_history line_trimmed history in
        let tokens = tokenize line_trimmed in
        try
          (match parse tokens with
           | ScriptBind b ->
               let final_lambda = desugar_equations [b] in
               let updated_env = StringMap.add b.fname final_lambda env in
               Printf.printf "Defined variable: %s\n" b.fname;
               repl updated_env updated_history script_file
           | REPLEval expr ->
               let start = Sys.time () in
               let result = whnf env expr in
               let duration = (Sys.time () -. start) *. 1000.0 in
               let rec check_string current acc =
                 match whnf env current with
                 | Nil ->
                     let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
                     Some (implode (List.rev acc))
                 | Cons (h, t) ->
                     (match whnf env h with Char c -> check_string t (c :: acc) | _ -> None)
                 | _ -> None
               in
               (match check_string result [] with
                | Some s ->
                    Printf.printf "Result:\n%s" s;
                    if String.length s > 0 && String.get s (String.length s - 1) = '\n' then () else print_endline ""
                | None -> Printf.printf "Result: %s\n" (print_node env result));
               Printf.printf "Evaluation time: %d ms\n" (int_of_float duration);
               repl env updated_history script_file)
        with
        | Failure msg -> Printf.printf "Lex/Parse Error: %s\n" msg; repl env updated_history script_file
        | Blackhole msg -> Printf.printf "Runtime Error: %s\n" msg; repl env updated_history script_file
        | RuntimeError msg -> Printf.printf "Runtime Error: %s\n" msg; repl env updated_history script_file
        | exn -> Printf.printf "Error: %s\n" (Printexc.to_string exn); repl env updated_history script_file

let print_output_node env target_node =
  let rec check_string current acc =
    match whnf env current with
    | Nil ->
        let rec implode chars = match chars with [] -> "" | c::cs -> String.make 1 c ^ implode cs in
        Some (implode (List.rev acc))
    | Cons (h, t) ->
        (match whnf env h with Char c -> check_string t (c :: acc) | _ -> None)
    | _ -> None
  in
  match check_string target_node [] with
  | Some s -> print_string s
  | None -> Printf.printf "%s\n" (print_node env target_node)

(* ========================================================================== *)
(* 7. SYSTEM ENTRY POINT                                                     *)
(* ========================================================================== *)

let main () =
  let args = Array.to_list Sys.argv in
  let script_file = match args with
    | _ :: [] -> "script.m"
    | _ :: f :: [] -> f
    | _ -> print_endline "Usage: miracula [script_file]"; exit 1
  in
  let is_repl_mode = (script_file = "script.m") in
  if is_repl_mode then (
    print_endline "==================================================";
    print_endline " Environment-Sharing OCaml REPL                     ";
    print_endline " Use '/e' to edit script.m, '/q' to exit          ";
    print_endline "=================================================="
  ) else (
    print_endline "==================================================";
    Printf.printf  " Loaded file: %s                  \n" script_file;
    Printf.printf  " Use '/e' to edit %s, '/q' to exit\n" script_file;
    print_endline "=================================================="
  );
  try
    let env_with_std = load_script_file "stdenv.m" StringMap.empty in
    let initial_env = load_script_file script_file env_with_std in
    repl initial_env [] script_file
  with
  | RuntimeError msg -> Printf.printf "Runtime Error: %s\n" msg; exit 1
  | Failure msg -> Printf.printf "Error: %s\n" msg; exit 1

let () = main ()
