(* ========================================================================== *)
(* 1. OPTIMIZED TYPE DEFINITIONS                                             *)
(* ========================================================================== *)

type var = string

module StringMap = Map.Make(String)

type thunk_state =
  | Unevaluated of node * env
  | Evaluating
  | Evaluated of node

and node =
  | Int of int
  | Var of var
  | Lam of var * node
  | App of node * node
  | Sub of node * node
  | Add of node * node
  | IfZero of node * node * node
  | Cons of node * node       
  | Nil                       
  | Thunk of thunk_state ref

and env = node StringMap.t

exception Blackhole of string

(* ========================================================================== *)
(* 2. LEXER WITH LIST SYMBOLS                                                *)
(* ========================================================================== *)

type token =
  | TOK_LAMBDA | TOK_DOT | TOK_ARROW | TOK_ASSIGN
  | TOK_LPAREN | TOK_RPAREN | TOK_LBRACK | TOK_RBRACK | TOK_COMMA
  | TOK_SUB | TOK_ADD
  | TOK_IFZERO | TOK_THEN | TOK_ELSE
  | TOK_INT of int
  | TOK_VAR of string
  | TOK_EOF

let tokenize str =
  let len = String.length str in
  let rec loop i acc =
    if i >= len then List.rev (TOK_EOF :: acc)
    else match str.[i] with
      | ' ' | '\t' | '\n' | '\r' -> loop (i + 1) acc
      | '\\' -> loop (i + 1) (TOK_LAMBDA :: acc)
      | '.'  -> loop (i + 1) (TOK_DOT :: acc)
      | '('  -> loop (i + 1) (TOK_LPAREN :: acc)
      | ')'  -> loop (i + 1) (TOK_RPAREN :: acc)
      | '['  -> loop (i + 1) (TOK_LBRACK :: acc)
      | ']'  -> loop (i + 1) (TOK_RBRACK :: acc)
      | ','  -> loop (i + 1) (TOK_COMMA :: acc)
      | '='  -> loop (i + 1) (TOK_ASSIGN :: acc)
      | '-'  -> if i + 1 < len && str.[i+1] == '>' then loop (i + 2) (TOK_ARROW :: acc) else loop (i + 1) (TOK_SUB :: acc)
      | '+'  -> loop (i + 1) (TOK_ADD :: acc)
      | '0'..'9' as c ->
          let rec read_num j num_str =
            if j < len && (match str.[j] with '0'..'9' -> true | _ -> false)
            then read_num (j + 1) (num_str ^ String.make 1 str.[j])
            else (j, int_of_string num_str)
          in
          let next_j, v = read_num (i + 1) (String.make 1 c) in
          loop next_j (TOK_INT v :: acc)
      | 'a'..'z' | 'A'..'Z' as c ->
          let rec read_var j var_str =
            if j < len && (match str.[j] with 'a'..'z' | 'A'..'Z' | '0'..'9' -> true | _ -> false)
            then read_var (j + 1) (var_str ^ String.make 1 str.[j])
            else (j, var_str)
          in
          let next_j, s = read_var (i + 1) (String.make 1 c) in
          let tok = match s with
            | "ifzero" -> TOK_IFZERO
            | "then"   -> TOK_THEN
            | "else"   -> TOK_ELSE
            | _        -> TOK_VAR s
          in
          loop next_j (tok :: acc)
      | _ -> failwith (Printf.sprintf "Lexer error: unexpected char %c" str.[i])
  in
  loop 0 []

(* ========================================================================== *)
(* 3. PARSER WITH LOOKAHEAD AND LIST DESUGARING                               *)
(* ========================================================================== *)

type parsed_pattern =
  | PatInt of int
  | PatVar of string

type raw_binding = {
  fname: string;
  pats: parsed_pattern list;
  body: node;
}

type stmt =
  | ScriptBind of raw_binding
  | REPLEval of node

let parse tokens =
  let toks = ref tokens in
  let peek () = List.hd !toks in
  let consume () = toks := List.tl !toks in

  let rec parse_expr () =
    match peek () with
    | TOK_LAMBDA ->
        consume ();
        begin match peek () with
        | TOK_VAR x ->
            consume ();
            if peek () <> TOK_DOT then failwith "Expected '.' after lambda variable";
            consume ();
            let body = parse_expr () in
            Lam (x, body)
        | _ -> failwith "Expected variable after lambda '\\'"
        end
    | TOK_IFZERO ->
        consume ();
        let cond = parse_expr () in
        if peek () <> TOK_THEN then failwith "Expected 'then'";
        consume ();
        let t_branch = parse_expr () in
        if peek () <> TOK_ELSE then failwith "Expected 'else'";
        consume ();
        let f_branch = parse_expr () in
        IfZero (cond, t_branch, f_branch)
    | _ -> parse_add_sub ()

  and parse_add_sub () =
    let rec loop left =
      match peek () with
      | TOK_ADD -> consume (); loop (Add (left, parse_app ()))
      | TOK_SUB -> consume (); loop (Sub (left, parse_app ()))
      | _ -> left
    in
    loop (parse_app ())

  and parse_app () =
    let rec loop left =
      match peek () with
      | TOK_INT _ | TOK_VAR _ | TOK_LPAREN | TOK_LBRACK ->
          loop (App (left, parse_atom ()))
      | _ -> left
    in
    loop (parse_atom ())

  and parse_atom () =
    match peek () with
    | TOK_INT n -> consume (); Int n
    | TOK_VAR x -> consume (); Var x
    | TOK_LPAREN ->
        consume ();
        let e = parse_expr () in
        if peek () <> TOK_RPAREN then failwith "Expected ')'";
        consume ();
        e
    | TOK_LBRACK ->
        consume ();
        parse_list_elements ()
    | _ -> failwith "Unexpected token inside atom expression"

  and parse_list_elements () =
    if peek () = TOK_RBRACK then begin
      consume ();
      Nil
    end else begin
      let head = parse_expr () in
      if peek () = TOK_COMMA then begin
        consume ();
        Cons (head, parse_list_elements ())
      end else if peek () = TOK_RBRACK then begin
        consume ();
        Cons (head, Nil)
      end else
        failwith "Expected ',' or ']' in list literal"
    end
  in

  let is_assignment () =
    let rec check = function
      | [] -> false
      | TOK_ASSIGN :: _ -> true
      | _ :: rest -> check rest
    in check !toks
  in

  if is_assignment () then begin
    match peek () with
    | TOK_VAR name ->
        consume ();
        let rec collect_patterns acc =
          match peek () with
          | TOK_INT n -> consume (); collect_patterns (PatInt n :: acc)
          | TOK_VAR x -> consume (); collect_patterns (PatVar x :: acc)
          | TOK_ASSIGN -> consume (); List.rev acc
          | _ -> failwith "Malformed equation left hand side"
        in
        let pats = collect_patterns [] in
        let expr_body = parse_expr () in
        ScriptBind { fname = name; pats = pats; body = expr_body }
    | _ -> failwith "Left hand side of binding must start with an identifier"
  end else begin
    let e = parse_expr () in
    if peek () <> TOK_EOF then failwith "Trailing tokens left unparsed";
    REPLEval e
  end

(* ========================================================================== *)
(* 4. ENVIRONMENT RUNTIME WITH NATIVE HD/TL PRIMITIVES                        *)
(* ========================================================================== *)

let rec whnf (env : env) : node -> node = function
  | Int n -> Int n
  | Lam (x, body) -> Lam (x, body)
  | Cons (h, t) -> Cons (h, t)
  | Nil -> Nil
  
  | Var x ->
      if x = "hd" || x = "tl" then 
        Var x
      else
        begin match StringMap.find_opt x env with
        | Some (Thunk r) ->
            begin match !r with
            | Evaluated n -> n
            | Evaluating  -> raise (Blackhole ("Infinite loop on identifier: " ^ x))
            | Unevaluated (expr, saved_env) ->
                r := Evaluating;
                let result = whnf saved_env expr in
                r := Evaluated result;
                result
            end
        | Some explicit_node -> whnf env explicit_node
        | None -> failwith ("Unbound variable: " ^ x)
        end
  
  | App (e1, e2) ->
      begin match whnf env e1 with
      | Var "hd" ->
          begin match whnf env e2 with
          | Cons (h, _) -> whnf env h
          | Nil -> failwith "Runtime Error: hd applied to empty list"
          | _ -> failwith "Runtime Error: hd expects a list"
          end
      | Var "tl" ->
          begin match whnf env e2 with
          | Cons (_, t) -> whnf env t
          | Nil -> failwith "Runtime Error: tl applied to empty list"
          | _ -> failwith "Runtime Error: tl expects a list"
          end
      | Lam (x, body) ->
          let shared_thunk = Thunk (ref (Unevaluated (e2, env))) in
          let extended_env = StringMap.add x shared_thunk env in
          whnf extended_env body
      | _ -> failwith "Runtime Error: Non-functional application"
      end

  | Sub (e1, e2) ->
      begin match whnf env e1, whnf env e2 with
      | Int n1, Int n2 -> Int (n1 - n2)
      | _ -> failwith "Runtime Error: Subtraction expects integers"
      end

  | Add (e1, e2) ->
      begin match whnf env e1, whnf env e2 with
      | Int n1, Int n2 -> Int (n1 + n2)
      | _ -> failwith "Runtime Error: Addition expects integers"
      end

  | IfZero (cond, t_branch, f_branch) ->
      begin match whnf env cond with
      | Int 0 -> whnf env t_branch
      | Int _ -> whnf env f_branch
      | _ -> failwith "Runtime Error: Condition must resolve to an integer"
      end

  | Thunk r ->
      begin match !r with
      | Evaluated n -> n
      | Evaluating  -> raise (Blackhole "Infinite loop inside generic thunk node")
      | Unevaluated (expr, saved_env) ->
          r := Evaluating;
          let result = whnf saved_env expr in
          r := Evaluated result;
          result
      end

let rec print_node env node =
  match node with
  | Int n -> string_of_int n
  | Lam (x, _) -> "\\" ^ x ^ ". <closure>"
  | Var x -> x
  | App (e1, e2) -> "(" ^ print_node env e1 ^ " " ^ print_node env e2 ^ ")"
  | Sub (e1, e2) -> "(" ^ print_node env e1 ^ " - " ^ print_node env e2 ^ ")"
  | Add (e1, e2) -> "(" ^ print_node env e1 ^ " + " ^ print_node env e2 ^ ")"
  | IfZero _ -> "<conditional>"
  | Thunk _ -> "<thunk>"
  | Nil -> "[]"
  | Cons _ ->
      let rec collect elements current =
        match whnf env current with
        | Cons (h, t) -> collect (print_node env h :: elements) t
        | Nil -> List.rev elements
        | rest -> List.rev (print_node env rest :: elements)
      in
      "[" ^ String.concat "," (collect [] node) ^ "]"

(* ========================================================================== *)
(* 5. SCRIPT COMPILER & DESUGARER FOR MULTIPLE EQUATIONS                      *)
(* ========================================================================== *)

let desugar_equations (eqs : raw_binding list) : node =
  match eqs with
  | [] -> failwith "Empty equation sequence"
  | [ { pats = []; body; _ } ] -> body
  | [ { pats = [PatVar x]; body; _ } ] -> Lam (x, body)
  | _ ->
      let first_eq = List.hd eqs in
      if List.exists (fun e -> List.length e.pats <> List.length first_eq.pats) eqs then
        failwith "Equations have mismatched parameter arities";
      
      let param_names = List.mapi (fun idx _ -> "p" ^ string_of_int idx) first_eq.pats in
      
      let rec build_decision_tree remaining_eqs =
        match remaining_eqs with
        | [] -> failwith "Pattern matching exhausted without catch-all"
        | eq :: rest ->
            let rec check_pats params patterns tree_body =
              match params, patterns with
              | [], [] -> tree_body
              | p :: p_rest, PatInt target_val :: pat_rest ->
                  IfZero (Sub (Var p, Int target_val), check_pats p_rest pat_rest tree_body, build_decision_tree rest)
              | p :: p_rest, PatVar binding_name :: pat_rest ->
                  let substituted_body = 
                    if binding_name = p then tree_body
                    else Lam (binding_name, tree_body) |> (fun l -> App (l, Var p))
                  in
                  check_pats p_rest pat_rest substituted_body
              | _ -> failwith "Internal pattern arity violation"
            in
            check_pats param_names eq.pats eq.body
      in
      let decision_tree = build_decision_tree eqs in
      List.fold_right (fun p acc -> Lam (p, acc)) param_names decision_tree

let load_script_file filename env =
  if not (Sys.file_exists filename) then begin
    Printf.printf "Script file '%s' not found. Starting with empty space.\n" filename;
    env
  end else
    let ic = open_in filename in
    let rec read_all lines =
      try
        let l = String.trim (input_line ic) in
        if l = "" || (String.length l >= 2 && String.sub l 0 2 = "||") then read_all lines
        else read_all (l :: lines)
      with End_of_file -> close_in ic; List.rev lines
    in
    let raw_lines = read_all [] in
    let bindings = List.map (fun l -> match parse (tokenize l) with ScriptBind b -> b | _ -> failwith "Invalid expression structure in script file") raw_lines in
    
    let grouped = List.fold_left (fun acc b ->
      let existing = if StringMap.mem b.fname acc then StringMap.find b.fname acc else [] in
      StringMap.add b.fname (existing @ [b]) acc
    ) StringMap.empty bindings in
    
    StringMap.fold (fun fname eq_list acc_env ->
      let final_lambda = desugar_equations eq_list in
      StringMap.add fname final_lambda acc_env
    ) grouped env

(* ========================================================================== *)
(* 6. REPL LOOP WITH SYSTEM EDITOR META COMMANDS                              *)
(* ========================================================================== *)

let rec repl (env : env) =
  print_string "miranda> ";
  flush stdout;
  match input_line stdin with
  | exception End_of_file -> print_endline "\nGoodbye."
  | "/q" -> print_endline "Goodbye."
  | "/e" ->
      print_endline "Opening vi script.m ...";
      let _ = Sys.command "vi script.m" in
      print_endline "Reloading environment profiles from script.m...";
      let reloaded_env = load_script_file "script.m" StringMap.empty in
      repl reloaded_env
  | "" -> repl env
  | line ->
      begin
        try
          let tokens = tokenize line in
          match parse tokens with
          | ScriptBind b ->
              let final_lambda = desugar_equations [b] in
              let updated_env = StringMap.add b.fname final_lambda env in
              Printf.printf "Defined variable: %s\n" b.fname;
              repl updated_env
          | REPLEval expr ->
              let start_time = Sys.time () in
              let result = whnf env expr in
              let end_time = Sys.time () in
              let duration_ms = (end_time -. start_time) *. 1000.0 in
              Printf.printf "Result: %s (Evaluated in %.4f ms)\n" (print_node env result) duration_ms;
              repl env
        with
        | Failure msg -> Printf.printf "Lex/Parse Error: %s\n" msg; repl env
        | Blackhole msg -> Printf.printf "Runtime Error: %s\n" msg; repl env
        | exn -> Printf.printf "Error: %s\n" (Printexc.to_string exn); repl env
      end

let () =
  print_endline "==================================================";
  print_endline " Miranda REPL with native Lists [hd, tl]          ";
  print_endline " Use '/e' to edit script.m, '/q' to exit          ";
  print_endline "==================================================";
  
  let initial_env = load_script_file "script.m" StringMap.empty in
  repl initial_env
