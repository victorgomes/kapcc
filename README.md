# kapcc
KA-based program correctness components

Modal Kleene algebras are relatives of dynamic logics that support program
construction and verification by equational reasoning. We describe their
application by implementing versatile program correctness components in
Isabelle/HOL. Starting from a weakest precondition based component with a simple
relational store model, we show how variants for Hoare logic, strongest
postconditions and program refinement can be built in a principled way.
Modularity of the approach is demonstrated by variants that capture program
termination and recursion, memory models for programs with pointers, and trace
semantics relevant to concurrency verification.

Also available in the Archive of Formal Proofs ([AFP](https://www.isa-afp.org/index.shtml)):<br/>
[Program Construction and Verification Components Based on Kleene Algebra](https://www.isa-afp.org/entries/Algebraic_VCs.shtml)
