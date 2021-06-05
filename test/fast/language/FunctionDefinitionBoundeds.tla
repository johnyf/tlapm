---------------------- MODULE FunctionDefinitionBoundeds -----------------------
(* Test that function definitions allow bounded declarations.

In other words, that the following form of definition
is allowed:
*)
f[x \in {TRUE}, y \in TRUE] == x
================================================================================
