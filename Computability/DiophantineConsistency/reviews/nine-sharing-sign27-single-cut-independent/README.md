# Independent 27-seed single-cut survey audit

The checker pins the 27-witness AST and selects all displayed positive
variable-minus-RHS cuts with self-independent natural addition/multiplication
right-hand sides. A separate variable-weight recursion computes the degree
after each substitution without rebuilding the substituted AST. It
reproduces all seven cases, their maximum syntactic degrees and the rows
attaining those maxima. The checker exited 0 using `python3 -I -S -B`.

This checks only the stated literal one-step, syntactic-degree restriction;
it proves no semantic lower bound, all-model bridge, or Lean theorem. Checker
SHA-256 `fd5774c6b2b985469e87654c38a93724d42c586d8f91f59d79d47256a09a25ab`;
result SHA-256
`9571bfaaa35b28130e2971f31601f840e40cc3f47a8df46941097a8189db3b43`.
