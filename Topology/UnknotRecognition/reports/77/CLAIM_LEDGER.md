# Claim ledger

This ledger accompanies the complete proofs in `paper/article.tex`.

| Claim | Article | Status and scope |
|---|---|---|
| Finite quotient detects every simple essential loop | Theorem 3.2 | Classical Livingston/Pikaart principle, rederived explicitly; closed marked orientable surface, simple-once promise |
| Scalar complementary-genus recovery | Theorem 3.2 | Proved; unordered genera only, conditioned on a verified simple curve |
| Central modulus g is necessary | Proposition 3.3 | Proved only in the stated scalar symplectic-area model |
| O(S g log^2(g+1)) evaluation | Theorem 4.2 | Proved and implemented, including exponent-bit scans and lazy generator setup; geometric source construction excluded |
| Narrow even-genus transport fails | Proposition 5.1 | Proved; explicit Dehn-twist counterexample, tested |
| Safe transport and minimal uniform modulus | Theorem 5.2, Proposition 5.3 | Proved in the stated group family; parity enlargement has classical precedent; a checked finite tuple is not a geometric certificate |
| Character nontrivial on both sides iff lift homology nonzero | Lemma 6.1 | Classical sufficient condition from Malestein–Putman, plus proved converse |
| Coisotropic interaction criterion | Theorem 7.3 | Proved here and implemented; no exhaustive literature-priority assertion |
| Exactly g+1 fixed double covers | Theorem 7.4 | Proved here under individual-lift-homology model; not a general algorithm lower bound |
| Quadratic genus ranks and cellular lift formula | Proposition 8.1, Theorem 8.2 | Proved; independent finite cross-checks |
| All class-two observers can miss a nontrivial nonsimple word | Section 9.1 | Proved with a free-group quotient and explicit freely reduced image |
| Observer preserves an externally established quasi-polynomial total | Corollary 9.1 | Conditional cost composition only; not a complete hierarchy algorithm |
| 47 unit tests and finite audits pass | Section 10, results/ | Actual final-run evidence; not a proof-assistant formalization |
| Compressed/literal local timing improvement | Section 10.3 | Measured only on explicit synthetic words, excluding source/parse/replay; not a native speedup |
| Scalar path uniformly faster than packed binary | Section 10.3 | Not claimed: final paired comparison has both gains and slowdowns |
| Ordered normal-orbit source adapter | Section 11 | Proposed; not implemented |
| General quasi-polynomial unknot recognition | Sections 9 and 12 | Not established by this report |

No manuscript or code in this package should be promoted into the recognizer
merely because the finite tests pass. The missing source-geometry obligations
are explicit, and the API never returns an `UNKNOT` verdict.
