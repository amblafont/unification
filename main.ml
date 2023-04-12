let rec map3 f l1 l2 l3 =
  match (l1, l2, l3) with
    ([], [],[]) -> []
  | (a1::l1, a2::l2, a3::l3) -> let r = f a1 a2 a3 in r :: map3 f l1 l2 l3
  | (_, _,_) -> invalid_arg "List.map3"


module type Signature =
  sig
    type arity
    type variableContext = arity
    type symbol
    type renaming

    val renamingToString : renaming -> string
    val symbolToString : symbol -> string

    val composeRenamings : renaming -> renaming -> renaming
    val renameSymbol : symbol -> renaming -> symbol
    val symbolArity : variableContext -> symbol -> arity list
    val arityFunctor : variableContext -> symbol -> renaming -> renaming list
    val pullback : renaming -> renaming -> arity * renaming * renaming
    val equaliser : renaming -> renaming -> arity * renaming
  end

module type BindingSignature =
  sig
    type symbol
    val arity : symbol -> int list
    val symbolToString : symbol -> string
  end

module SignatureOfBSig (S : BindingSignature) =
  struct 
  type arity = int
type variableContext = arity
type symbol = 
    O of S.symbol
  | Var of int
type renaming = int list

let symbolToString : symbol -> string = function Var n -> string_of_int n 
  | O o -> S.symbolToString o


let renv (x : arity)(r : renaming) : arity =
  List.nth r (x - 1)

let renamingToString (l : renaming) : string =
  String.concat ", " (List.map Int.to_string l)

let renameSymbol (o : symbol) (x : renaming) = match o with
  Var n -> Var (renv n x)
  |_ -> o;;

let symbolArity (n : variableContext) = function
  Var _ -> []
| O o -> List.map ((+) n) (S.arity o)


let composeRenamings (x : renaming)(y : renaming) : renaming = 
    List.map (fun n -> renv n y) x

let equaliser (x : renaming)(y : renaming) : arity * renaming = 
   let rec aux idx l1 l2 = 
    match l1, l2 with
      [], [] -> []
     | t1 :: q1, t2 :: q2 ->
        if t1 = t2 then idx :: aux (idx + 1) q1 q2 else aux (idx + 1) q1 q2
    | _ -> failwith "invalid arg: equaliser_lc"
      in
    let z = aux 1 x y in
     List.length z, z


let rec find_idx (x : 'a) = function [] -> raise Not_found
   | t :: q ->
      if t = x then 
        1
    else
      1 + find_idx x q
      
let pullback (x : renaming)(y : renaming) : arity * renaming * renaming = 
        let rec aux1 idx l1 : renaming * renaming = 
         match l1 with
           [] -> [], []
          | t1 :: q1  ->
             let (p,q) = aux1 (idx + 1) q1 in
             try let i = find_idx t1 y in
             (idx::p, i :: q)
             with
             Not_found -> (p,q)
           in
           let (l1, l2) = aux1 1 x in
           (List.length l1, l1, l2)

let rec arityFunctor (n : arity) (o : symbol) (r : renaming) : renaming list =
   match o with 
   Var _ -> []
   | O o ->
     List.map (fun ar -> r @ List.init ar (fun p -> n + p + 1)) (S.arity o)
end

(*** 

Example: lambda calculus

** *)

module LambdaCalculusBSig = struct 

type symbol = App | Abs
let arity = function App -> [0; 0] | Abs -> [1];;

let symbolToString = function App -> "@" | Abs -> "λ"

end

module LambdaCalculus = SignatureOfBSig(LambdaCalculusBSig)

(* module LCSig : Signature = struct 
  include LambdaCalculus;;
end *)

(* 
   
Unification algorithm

*)

module Unification (S : Signature) = struct
  exception NoUnifier
  open S
  type name = string

  type syntax = 
    Op of symbol * syntax list
  | MVar of name * renaming

  let rec syntaxToString = 
    function 
      MVar (n, r) -> n ^ "(" ^ renamingToString r ^ ")"
    | Op (o, l) -> if l = [] then symbolToString o else
      symbolToString o ^ "(" ^ 
           (String.concat ", " 
             (List.map syntaxToString l)) 
             ^ ")" ;;
  
  let rec renameSyntax (variableContext : arity) (t : syntax) (r : renaming) : syntax =
     (match t with
       MVar (n, x) -> MVar (n, composeRenamings r x)
     | Op  (o, argument) -> Op (renameSymbol o r, 
          map3 renameSyntax 
            (symbolArity variableContext o) 
            argument 
            (arityFunctor variableContext o r)));;
           

  type substitution = (name * arity * syntax) list

  let substitutionToString (sigma : substitution) : string =
    String.concat ", " 
     (List.map (function (n, _, t) -> n ^ " ↦ " ^ 
             syntaxToString t) sigma)

  let rec substitute (t : syntax)(sigma : substitution) : syntax =
    match t with
      Op (o, args) -> Op (o, List.map (fun t -> substitute t sigma)  args)
    | MVar (name, x) -> 
         try 
          let _, a, u = (List.find (fun (name2, _, _) -> name == name2) sigma) in 
              renameSyntax a u x 
         with
             Not_found -> MVar (name,x)
  
  let rec composeSubstitution (sigma1 : substitution) (sigma2 : substitution) =
             (List.map (function (x,a,t) -> (x,a, substitute t sigma2)) sigma1) 
                    @ sigma2
           

  let id_substitution : substitution = []

  let replaceMVar (x : name)(a : arity) (t : syntax) (sigma : substitution) 
    : substitution = (x, a, t)::sigma


  let rec occur_check (x : name)(t : syntax) : bool =
      match t with
       MVar (n, _) -> x == n
       | Op (_, l) -> List.exists (occur_check x) l

  let rec prune (variableContext : variableContext) (t : syntax)(x : 'renaming) :
       (syntax * substitution) = 
       match t with
       | Op (o, args) -> 
           let (ws, sigma) = prune_list (symbolArity variableContext o) args (arityFunctor variableContext o x) in
             Op (o, ws), sigma
       | MVar (name, y) ->
           let (newArity, p, q) = pullback x y in
           MVar(name, p), replaceMVar name newArity (MVar (name, q)) id_substitution
  
  and prune_list (variableContexts : variableContext list) 
     (ts : syntax list) (xs : renaming list) 
  :  syntax list * substitution  = 
     match variableContexts, ts, xs with
       [], [], [] -> [], id_substitution
     | a1 :: al1, t1 :: q1 , x1 :: x2 -> 
        let (w1, sigma1) = prune a1 t1 x1 in
        let q1s = List.map (fun t -> substitute t sigma1) q1 in 
        let (w2, sigma2) = prune_list al1 q1s x2 in 
            (substitute w1 sigma2 :: w2), composeSubstitution sigma1 sigma2
     | _ -> failwith "invalid args: prune-list"


  let rec unify variableContext (t : syntax)(u : syntax) : substitution = match t,u with
     Op (o1, _), Op (o2, _) when o1 <> o2 -> raise NoUnifier
   | Op (o, l1), Op (_, l2) -> unify_list (symbolArity variableContext o) l1 l2
   | MVar (name, x1),  MVar (name2, x2) when name = name2 -> 
         let (newArity, y) = equaliser x1 x2 in
         id_substitution 
         |> replaceMVar name newArity (* UNSURE!! *)
         (MVar(name, y))
   | MVar (name, x), v | v, MVar (name, x) ->
        if occur_check name v then
           raise NoUnifier
        else
           let (w, sigma) = prune variableContext v x in
           replaceMVar name variableContext w sigma (* UNSURE!! *)
 
 
                 
 and unify_list (variableContexts : variableContext list) ts us = 
   match variableContexts, ts, us with
     [], [], [] -> id_substitution
     | a1 :: al1, t1 :: q1 , t2 :: q2 -> 
        let sigma1 = unify a1 t1 t2 in
        let mapsigma = List.map (fun t -> substitute t sigma1) in 
        let sigma2 = unify_list al1 (mapsigma q1) (mapsigma q2) in 
            composeSubstitution sigma1 sigma2
     | _ -> failwith "invalid args: unify_list"
end


module LCUnification = Unification(LambdaCalculus)

let unify_lc (n : LambdaCalculus.variableContext)(t : LCUnification.syntax) u : string =
  LCUnification.unify n t u |> LCUnification.substitutionToString

open LCUnification;;

unify_lc 3 (MVar ("M", [1; 2])) (MVar ("M", [2; 1]));;
unify_lc 3 (MVar ("M", [1; 3])) (MVar ("M", [2;3]));;
unify_lc 3 (MVar ("M", [1; 2])) (MVar ("N", [2; 1]));;
