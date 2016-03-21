(* Language specific syntax *)
(*--------------------------*)
syntax Exp          ::= ... | Exp ":" ExpPattern | ...
syntax Term         ::= ...
                      | Var "=" Exp                                 (* assignment *)
                      | Term ":" TermPattern                        (* pretty predicates *)
                      | ...

(* CTL spatial quantifiers *)
(*-------------------------*)
syntax CTLQuant     ::= "A"                                         (* for all paths *)
                      | "E"                                         (* exists a path *)

(* CTL Logic Connectives *)
(*-----------------------*)
syntax InstPattern  ::= Term                                        (* language specific *)
                      | Var ":" InstPattern                         (* name a pattern *)
                      | enter                                       (* entrance node *)
                      | exit                                        (* exit nodes *)
                      | "not" InstPattern                           (* `not` *)
                      | InstPattern " " InstPattern                 (* `and` *)
                      | InstPattern "|" InstPattern                 (* `or` *)
                      | "--" CTLQuant ">" InstPattern               (* `next` *)
                      | InstPattern "<" CTLQuant "--"               (* backwards `next` *)
                      | "--" CTLQuant InstPattern "->" InstPattern  (* `until` *)
                      | InstPattern "<-" CTLQuant InstPattern "--"  (* backwards `until` *)
                      | "--" CTLQuant "->"                          (* `eventually` *)
                      | "<-" CTLQuant "--"                          (* backwards `eventually` *)

(*
    Can get `always` forwards:  "--" CTLQuant InstPattern "->" exit
    Can get `always` backwards: enter "<-" CTLQuant InstPattern "--"
*)

(* Syntax for defining patterns *)
(*------------------------------*)
syntax PatternDef   ::= "pattern" "[" PatternName List{Var} "]" ":" InstPattern

(* Transformation rule syntax *)
(*----------------------------*)
syntax Rule         ::= InstPattern "=>" InstPattern
                      | InstPattern "=>" InstPattern if InstPattern

(* Define a transformation rule *)
(*------------------------------*)
syntax RuleDef      ::= "rule" "[" RuleName "]" ":" List{Rule}

(* How to build composite transformations *)
(*----------------------------------------*)
syntax Strategy     ::= RuleName                                    (* apply rule once *)
                      | StrategyName                                (* apply strategy once *)
                      | Strategy "*"                                (* apply many *)
                      | Strategy ";" Strategy [left]                (* sequence *)

(* Name a list of rules as belonging to a transformation *)
(*-------------------------------------------------------*)
syntax StrategyDef  ::= "strategy" "[" StrategyName "]" ":" Strategy
