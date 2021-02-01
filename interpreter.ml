(* utility functions *)

let rec implode (cs: char list): string =
  match cs with
  | c :: cs -> (String.make 1 c) ^ implode cs
  | [] -> ""

let rec explode (s: string): char list =
  let len = String.length s in
  let rec loop i =
    if i < len then (String.get s i) :: loop (i + 1)
    else []
  in loop 0

let readlines fname =
  let ic = open_in fname in
  let rec loop ic =
    match input_line ic with
    | s -> s :: loop ic
    | exception _ -> []
  in
  let s = loop ic in
  let () = close_in ic in
  s

(* Abstract syntax *)

type name = string

type value =
  | B of bool
  | I of int
  | S of string
  | N of name
  | U
  | E
  | C of value * value * (command list) * env (* closure type *)
(* | C of name * name * (command list) * env *)

and command =
  | Push of value | Swap | Pop
  | Add | Sub | Mul | Div | Rem | Neg
  | And | Or  | Not | Lt  | Lte | Gt | Gte | Eq  | Cat
  | Bnd | Call | Return
  | BeginEnd of commands
  | IfThenElse of commands * commands * commands
  | FunEndFun of value * value * commands
(*  | FunEndFun of name * name * commands *)
  | TryWith of commands * commands
  | Quit

and commands = command list

and stack = value list

and env = (string * value) list

let fprint_value oc cst =
  Printf.
    (match cst with
     | B b -> fprintf oc "<%b>" b
     | I i -> fprintf oc "%d" i
     | S s -> fprintf oc "%s" s
     | N n -> fprintf oc "%s" n
     | U -> fprintf oc "<unit>"
     | E -> fprintf oc "<error>"
     | C (a, b, c, d) -> fprintf oc "<closure>")

let fprint_values oc vals =
    List.iter (fprint_value oc) vals

let rec fprint_command oc com =
  Printf.
    (match com with
     | Push cst ->
       fprintf oc "Push %a\n" fprint_value cst;
     | Swap -> fprintf oc "Swap\n"
     | Pop -> fprintf oc "Pop\n"
     | Add -> fprintf oc "Add\n"
     | Sub -> fprintf oc "Sub\n"
     | Mul -> fprintf oc "Mul\n"
     | Div -> fprintf oc "Div\n"
     | Rem -> fprintf oc "Rem\n"
     | Neg -> fprintf oc "Neg\n"
     | And -> fprintf oc "And\n"
     | Or  -> fprintf oc "Or\n"
     | Not -> fprintf oc "Not\n"
     | Lt  -> fprintf oc "Lt\n"
     | Lte -> fprintf oc "Lte\n"
     | Gt  -> fprintf oc "Gt\n"
     | Gte -> fprintf oc "Gte\n"
     | Eq  -> fprintf oc "Eq\n"
     | Cat -> fprintf oc "Cat\n"
     | Bnd -> fprintf oc "Bnd\n"
     | Call -> fprintf oc "Call\n"
     | Return -> fprintf oc "Return\n"
     | BeginEnd coms ->
       fprintf oc "Begin\n%aEnd\n"
         fprint_commands coms;
     | IfThenElse (coms1, coms2, coms3) ->
       fprintf oc "If\n%aThen\n%aElse\n%aEndIf\n"
         fprint_commands coms1
         fprint_commands coms2
         fprint_commands coms3
     | FunEndFun (fname, arg, coms) ->
        fprintf oc "Fun\n%a%a%a\n"
         fprint_value fname (* fprint_name (N fname) *)
         fprint_value arg
         fprint_commands coms
     | TryWith (coms1, coms2) ->
        fprintf oc "Try\n%aWith\n%aEndTry\n"
         fprint_commands coms1
         fprint_commands coms2
     | Quit -> fprintf oc "Quit\n")

and fprint_commands oc coms =
  List.iter (fprint_command oc) coms

let fprint_stack oc st =
  Printf.
    (List.iter (fun sv -> fprint_value oc sv; fprintf oc "\n") st)

let print_value = fprint_value stdout
let print_values = fprint_values stdout
let print_command = fprint_command stdout
let print_commands = fprint_commands stdout
let print_stack = fprint_stack stdout

(* Parser *)

type 'a parser = char list -> 'a option * char list

let return (a: 'a): 'a parser  = fun cs -> (Some a, cs)

let bind (p: 'a parser) (f: 'a -> 'b parser): 'b parser =
  fun cs ->
  let a, cs' = p cs in
  match a with
  | Some a -> f a cs'
  | None -> (None, cs)

let (let*) = bind

let (|>>) (p: 'a parser) (f: 'a -> 'b): 'b parser =
  let* a = p in
  return (f a)

let (>>) (p: 'a parser) (q: 'b parser): 'b parser =
  let* _ = p in
  q

let (<<) (p: 'a parser) (q: 'b parser): 'a parser =
  let* a = p in
  let* _ = q in
  return a

let fail: 'a parser = fun cs -> (None, cs)

let delay (): unit parser = return ()

let (<|>) (p: 'a parser) (q: 'a parser): 'a parser =
  fun cs ->
  match p cs with
  | (Some a, cs) -> (Some a, cs)
  | (None, _) -> q cs

let choice (ps: 'a parser list): 'a parser =
  List.fold_right (fun p acc -> p <|> acc) ps fail

let rec many (p: 'a parser): 'a list parser =
  (let* a = p in
   let* ls = many p in
   return(a :: ls))
  <|>
  return[]

let many1 (p: 'a parser): 'a list parser =
  let* a = p in
  let* ls = many p in
  return(a :: ls)

let opt (p: 'a parser): 'a option parser =
  (let* a = p in
   return (Some a))
  <|>
  return None

let read: char parser =
  fun cs ->
  match cs with
  | c :: cs -> (Some c, cs)
  | [] -> (None, cs)

let rec readn (n: int): string parser =
  if n > 0 then
    let* c = read in
    let* cs = readn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let rec peak: char parser =
  fun cs ->
  match cs with
  | c :: _ -> (Some c, cs)
  | [] -> (None, cs)

let rec peakn (n: int): string parser =
  if n > 0 then
    let* c = read in
    let* cs = peakn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let sat (f: char -> bool): char parser =
  let* c = read in
  if f c then return c
  else fail

let char (c: char): char parser =
  sat ((=) c)

let digit: char parser =
  sat (fun x -> '0' <= x && x <= '9')

let lower: char parser =
  sat (fun x -> 'a' <= x && x <= 'z')

let upper: char parser =
  sat (fun x -> 'A' <= x && x <= 'Z')

let alpha: char parser =
  lower <|> upper

let alphanum: char parser =
  alpha <|> digit

let string (str: string): unit parser =
  let len = String.length str in
  let* str' = readn len in
  if str = str' then return ()
  else fail

let w: unit parser =
  let* _ = sat (String.contains " \r\n\t") in
  return ()

let ws: unit parser =
  let* _ = many w in
  return ()

let ws1: unit parser =
  let* _ = w in
  let* _ = ws in
  return ()

let reserved (s: string): unit parser =
  string s >> ws

let delimit l p r =
  let* _ = l in
  let* res = p in
  let* _ = r in
  return res

let int: int parser =
  let* sgn = opt (reserved "-") in
  let* cs = many1 digit in
  let n = List.fold_left
      (fun acc c -> acc * 10 + (int_of_char c) - (int_of_char '0'))
      0 cs
  in
  match sgn with
  | Some _ -> return (-n)
  | None -> return n

let bool: bool parser =
  (string "<true>" >> return true) <|>
  (string "<false>" >> return false)

let error: unit parser =
  string "<error>"

let unit: unit parser =
  string "<unit>"

let str: string parser =
  let* cs = delimit (char '"') (many (sat ((!=) '"'))) (char '"') in
  return (implode cs)

let name: string parser =
  let* os = many (char '_') in
  let* c = alpha in
  let* cs = many (alphanum <|> char '_') in
  return ((implode os) ^ (implode (c :: cs)))

let value: value parser =
  choice
    [ (int   |>> fun n -> I n);
      (bool  |>> fun b -> B b);
      (error |>> fun e -> E);
      (str   |>> fun s -> S s);
      (name  |>> fun n -> N n);
      (unit  |>> fun u -> U); ]

let push: command parser =
  let* _ = reserved "Push" in
  let* cst = value << ws in
  return (Push cst)

let swap: command parser =
  let* _ = reserved "Swap" in
  return Swap

let pop: command parser =
  let* _ = reserved "Pop" in
  return Pop

let add: command parser =
  let* _ = reserved "Add" in
  return Add

let sub: command parser =
  let* _ = reserved "Sub" in
  return Sub

let mul: command parser =
  let* _ = reserved "Mul" in
  return Mul

let div: command parser =
  let* _ = reserved "Div" in
  return Div

let rem: command parser =
  let* _ = reserved "Rem" in
  return Rem

let neg: command parser =
  let* _ = reserved "Neg" in
  return Neg

let and': command parser =
  let* _ = reserved "And" in
  return And

let or': command parser =
  let* _ = reserved "Or" in
  return Or

let not': command parser =
  let* _ = reserved "Not" in
  return Not

let lt: command parser =
  let* _ = reserved "Lt" in
  return Lt

let lte: command parser =
  let* _ = reserved "Lte" in
  return Lte

let gt: command parser =
  let* _ = reserved "Gt" in
  return Gt

let gte: command parser =
  let* _ = reserved "Gte" in
  return Gte

let eq: command parser =
  let* _ = reserved "Eq" in
  return Eq

let cat: command parser =
  let* _ = reserved "Cat" in
  return Cat

let bnd: command parser =
  let* _ = reserved "Bnd" in
  return Bnd

let quit: command parser =
  let* _ = reserved "Quit" in
  return Quit

let call: command parser =
  let* _ = reserved "Call" in
  return Call

let return': command parser =
  let* _ = reserved "Return" in
  return Return

let rec beginEnd (): command parser =
  let* _ = reserved "Begin" in
  let* coms = commands () in
  let* _ = reserved "End" in
  return (BeginEnd coms)

and ifThenElse (): command parser =
  let* _ = reserved "If" in
  let* coms1 = commands () in
  let* _ = reserved "Then" in
  let* coms2 = commands () in
  let* _ = reserved "Else" in
  let* coms3 = commands () in
  let* _ = reserved "EndIf" in
  return (IfThenElse (coms1, coms2, coms3))

and funEndFun (): command parser =
    let* _ = reserved "Fun" in
    let* fname = value << ws in (* name << ws *)
    let* arg = value << ws in
    let* coms = commands () in
    let* _ = reserved "EndFun" in
    return (FunEndFun (fname, arg, coms))

and tryWith (): command parser =
    let* _ = reserved "Try" in
    let* coms1 = commands () in
    let* _ = reserved "With" in
    let* coms2 = commands () in   
    let* _ = reserved "EndTry" in
    return (TryWith (coms1, coms2))

and command () =
  choice
    [ push; swap; pop;
      add; sub; mul; div; rem; neg;
      and'; or'; not';
      lte; lt; gte; gt; eq;
      cat;
      bnd;
      call; return';
      beginEnd();
      ifThenElse();
      funEndFun();
      tryWith();
      quit; ]

and commands () =
  many1 (command ())

(* helper function to check for presence of error in stack -- is it "ok"? *)

let rec ok_status b =
  match b with
  | x::y -> if ((x != E) = true) then (ok_status y) else false
  | [] -> true

(* evaluation *)

let get x (env: env) =
  match x with
  | N n -> List.assoc_opt n env
  | x -> Some x

let get_int x env =
  match get x env with
  | Some (I i) -> Some i
  | _ -> None

let get_bool x env =
  match get x env with
  | Some (B b) -> Some b
  | _ -> None

let get_string x env =
  match get x env with
  | Some (S s) -> Some s
  | _ -> None

let get_name x =
  match x with
  | N n -> Some n
  | _ -> None

type result =
  | Ok of stack
  | Exit of stack

let rec interp coms stack env =
  match coms, stack with
  | Push v :: coms, _ ->
    interp coms (v :: stack) env
  | Swap :: coms, x :: y :: stack ->
    interp coms (y :: x :: stack) env
  | Pop :: coms, x :: stack ->
    interp coms stack env
  | Add :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (I (x + y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Sub :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (I (x - y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Mul :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (I (x * y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Div :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some 0 -> interp coms (E :: stack) env
     | Some x, Some y -> interp coms (I (x / y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Rem :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some 0 -> interp coms (E :: stack) env
     | Some x, Some y -> interp coms (I (x mod y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Neg :: coms, x :: stack' ->
    (match get_int x env with
     | Some x -> interp coms (I (-x) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Cat :: coms, x :: y :: stack' ->
    (match get_string x env, get_string y env with
     | Some x, Some y -> interp coms (S (x ^ y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | And :: coms, x :: y :: stack' ->
    (match get_bool x env, get_bool y env with
     | Some x, Some y -> interp coms (B (x && y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Or :: coms, x :: y :: stack' ->
    (match get_bool x env, get_bool y env with
     | Some x, Some y -> interp coms (B (x || y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Not :: coms, x :: stack' ->
    (match get_bool x env with
     | Some x -> interp coms (B (not x) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Lt :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (B (x < y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Lte :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (B (x <= y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Gt :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (B (x > y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Gte :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (B (x >= y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Eq :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> interp coms (B (x = y) :: stack') env
     | error -> interp coms (E :: stack) env)
  | Bnd :: coms, x :: y :: stack' ->
    (match get_name x, get y env with
     | Some x, Some E -> interp coms (E :: stack) env
     | Some x, Some y -> interp coms (U :: stack') ((x, y) :: env)
     | error -> interp coms (E :: stack) env)
  | (BeginEnd local) :: coms, _ ->
    (match interp local stack env with
     | Ok (sv :: _) -> interp coms (sv :: stack) env
     | Exit (stack) -> Exit stack
     | error -> interp coms (E :: stack) env)
  | (IfThenElse (coms1, coms2, coms3)) :: coms, _ ->
    (match interp coms1 stack env with
     | Ok (sv :: _) ->
       (match get_bool sv env with
        | Some b ->
          (if b then
             match interp coms2 stack env with
             | Ok (sv :: _) -> interp coms (sv :: stack) env
             | Exit stack -> Exit stack
             | error -> interp coms (E :: stack) env
           else
             match interp coms3 stack env with
             | Ok (sv :: _) -> interp coms (sv :: stack) env
             | Exit stack -> Exit stack
             | error -> interp coms (E :: stack) env)
        | error -> interp coms (E :: stack) env)
     | Exit stack -> Exit stack
     | error -> interp coms (E :: stack) env)
  | (FunEndFun (fname, arg, coms')) :: coms, _ ->
    (match get_name fname with
      | Some fname' -> interp coms (U :: stack) ((fname', C (fname, arg, coms', env)) :: env)
      | _ -> interp coms (E :: stack) env)
    (* | error -> interp coms (E :: stack) env) *)
  | ((TryWith (coms1, coms2)) :: coms, _) ->
        (let try_with_update u =
            match u with
            | x::y -> x
            | [] -> E
          in
        (match (interp coms1 stack env) with 
        (* successful coms1 -> top element kept and rest restored *)
            | Ok a ->    
                (* successful coms2 -> top element kept and rest restored *)
                if (ok_status a) then interp coms ((try_with_update a)::stack) env else (interp coms2 stack env) 
            | _ -> Exit stack
        )
        )
  | (Return :: coms, (x::y)) ->
        (match (get x env) with 
            (* | Some a -> Ok stack (* continue *) *)
            | Some a -> Ok [a] (* continue *)
            | _ -> Exit stack (* discontinue *))
  | Call :: coms, x :: y :: stack ->
    (match get x env, get y env with
      | Some x', Some y' -> (match y' with
        | C (fname, arg', coms', env') -> (match get_name arg', get_name fname with
          | Some arg'', Some fname' -> (match interp coms' stack ((arg'', x')::(fname', C (fname, N arg'', coms', env'))::env') with
            | Ok (h::t) -> interp coms (h::stack) env
            | Ok [] -> interp coms (E::x::y::stack) env
            | Exit stack -> Exit stack)
          | _ -> Ok stack)
        | _ -> Ok stack)
      | error -> interp coms (E::x::y::stack) env
    )
  | Quit :: coms, _ -> Exit stack
  | [], _ -> Ok stack
  | _ :: coms, _ -> interp coms (E :: stack) env

(* testing *)

let parse fname =
  let strs = readlines fname in
  let css = List.map explode strs in
  let cs = List.fold_right (fun cs acc -> cs @ ['\n'] @ acc) css [] in
  match (ws >> commands ()) cs with
  | Some coms, [] -> coms
  | _, cs -> failwith (implode cs)

let interpreter (inputFile : string) (outputFile : string) =
  let coms = parse inputFile in
  let oc = open_out outputFile in
  let _ =
    match interp coms [] [] with
    | Ok stack -> fprint_stack oc stack
    | Exit stack -> fprint_stack oc stack
  in
  close_out oc
