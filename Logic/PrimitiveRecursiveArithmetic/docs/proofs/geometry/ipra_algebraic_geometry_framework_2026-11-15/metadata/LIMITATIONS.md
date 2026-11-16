# Limitations and formal boundary

1. The main report contains complete ordinary mathematical proofs, but no new main theorem is yet a compiled `Prf PRAAx` object.
2. The Lean files are blueprints and target definitions. No Lean executable or ProveIt dependency closure was present in the preparation environment.
3. Python tests validate finite implementations; they are not formal proofs and not an iPRA proof checker.
4. The finite atlas language handles schemes through chosen presentations and overlap certificates. It does not internalize the class of all prime ideals as a completed infinite space.
5. The projective-space result is first an exact computation of the standard finite Čech complex. Agreement with conventional derived-functor sheaf cohomology uses the standard affine acyclicity/comparison theorem; fully formalizing that metatheory inside iPRA is a separate project.
6. Certificate verification is separated from certificate production. A quotient equality witness, Gröbner certificate, cover certificate, height bound, or descent representative must be supplied or produced by a separately proved algorithm.
7. No general positive height bound, complete rational-point list, or unrestricted branch selector is inferred from the geometric framework.
