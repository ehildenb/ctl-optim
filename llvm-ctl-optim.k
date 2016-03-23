requires "llvm-semantics.k"

module CTL-SYNTAX

    syntax Var          ::= String
    syntax Name         ::= String
    /* Language specific syntax */
    /*--------------------------*/
    // syntax Exp          ::= ... | Exp ":" ExpPattern | ...
    // syntax Term         ::= ...
    //                       | Var "=" Exp                                 /* assignment */
    //                       | Term ":" TermPattern                        /* pretty predicates */
    //                       | ...

    /* CTL spatial quantifiers */
    /*-------------------------*/
    syntax CTLQuant     ::= "A"                                         /* for all paths */
                          | "E"                                         /* exists a path */

    /* CTL Logic Connectives */
    /*-----------------------*/
    syntax InstPattern  ::= InstPattern ":" InstPattern                 /* name a pattern */
                          | "enter"                                     /* entrance node */
                          | "exit"                                      /* exit nodes */
                          | "not" InstPattern                           /* `not` */
                          | InstPattern " " InstPattern                 /* `and` */
                          | InstPattern "|" InstPattern                 /* `or` */
                          | "--" CTLQuant ">" InstPattern               /* `next` */
                          | InstPattern "<" CTLQuant "--"               /* backwards `next` */
                          | "--" CTLQuant InstPattern "->" InstPattern  /* `until` */
                          | InstPattern "<-" CTLQuant InstPattern "--"  /* backwards `until` */
                          | "--" CTLQuant "->"                          /* `eventually` */
                          | "<-" CTLQuant "--"                          /* backwards `eventually` */

    /* Syntax for defining patterns */
    /*------------------------------*/
    syntax PatternName  ::= Name
                          | PatternName PatternName [left]
    syntax PatternDef   ::= "pattern" "[" PatternName "]" ":" InstPattern

    /* Transformation rule syntax */
    /*----------------------------*/
    syntax Rule         ::= InstPattern "=>" InstPattern
                          | InstPattern "=>" InstPattern "if" InstPattern
                          | Rule Rule [left]

    /* Define a transformation rule */
    /*------------------------------*/
    syntax RuleName     ::= Name
    syntax RuleDef      ::= "rule" "[" RuleName "]" ":" Rule

    /* How to build composite transformations */
    /*----------------------------------------*/
    syntax StrategyName ::= RuleName
    syntax Strategy     ::= RuleName                                    /* apply rule once */
                          | StrategyName                                /* apply strategy once */
                          | Strategy "*"                                /* apply many */
                          | Strategy ";" Strategy [left]                /* sequence */

    /* Name a list of rules as belonging to a transformation */
    /*-------------------------------------------------------*/
    syntax StrategyDef  ::= "strategy" "[" StrategyName "]" ":" Strategy

endmodule


module LLVM-CTL-OPTIM
    imports CTL-SYNTAX
    imports LLVM-SYNTAX
endmodule
