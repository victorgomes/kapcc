# kapcc
KA-based program correctness components

Modal Kleene algebras are relatives of dynamic logics that support program construction
and verification by equational reasoning. We describe their application in implementing
versatile program correct- ness components in interactive theorem provers such as
Isabelle/HOL. Starting from a weakest precondition based component with a simple relational
store model, we show how variants for Hoare logic, strongest postconditions and program
refinement can be built in a principled way. Modularity of the approach is demonstrated
by variants that capture program termination and recursion, memory models for programs
with pointers, and trace semantics relevant to concurrency verification.
