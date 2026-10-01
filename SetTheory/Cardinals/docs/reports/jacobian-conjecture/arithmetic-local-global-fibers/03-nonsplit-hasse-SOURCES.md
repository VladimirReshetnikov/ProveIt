# Source and attribution ledger

All sources reviewed on September 30, 2026. Repository content was read through
the GitHub connector; public primary literature was checked on the web.

## Pinned ProveIt sources

Commit: `6d04e1e385f2fe7d1cfbdbd8fd8d4e45bd6b6c72`.

1. Formal map and determinant:
   `Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean`
   https://github.com/VladimirReshetnikov/ProveIt/blob/6d04e1e385f2fe7d1cfbdbd8fd8d4e45bd6b6c72/Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean

   Used to identify the literal map and the existing formal declarations.
   Its Lean build was not rerun. The determinant and inverse identities used here
   were independently checked by exact symbolic arithmetic.

2. Prior arithmetic report:
   `SetTheory/Cardinals/docs/reports/jacobian-conjecture/arithmetic-local-global-fibers/article.tex`
   https://github.com/VladimirReshetnikov/ProveIt/blob/6d04e1e385f2fe7d1cfbdbd8fd8d4e45bd6b6c72/SetTheory/Cardinals/docs/reports/jacobian-conjecture/arithmetic-local-global-fibers/article.tex

   Also read the README in the same directory. The merged report contains a
   September 24 manuscript and a September 29 manuscript added September 30.
   Part I Section 12.2 asks for local integral solubility in the split and then
   rational-plus-quadratic sectors. Its update says the nonsplit sector remains
   open. Section 12.3 asks for target-height asymptotics. Part II settles the
   completely split sector, not the nonsplit one, and asks for coefficient-level
   certificates. The reported split law on C=2 is
   27 Gamma(1/3)^2 / (8 pi^2 Gamma(2/3)) * T^(2/3).

   The present proof rederives its required root chart. It does not depend on
   the prior unformalized split counting proof. The dyadic image measure and
   rational Hasse mechanism are attributed rather than claimed anew.

3. Research-report index and provenance:
   `SetTheory/Cardinals/docs/reports/README.md` and
   `SetTheory/Cardinals/README.md` at the same pin.
   Used to understand scope, report placement, and the distinction between
   research manuscripts and formal developments.

## External primary sources

4. Shuhong Gao, Counterexamples to the Jacobian conjecture in dimensions greater
   than two, arXiv:2608.00222v1, July 31, 2026.
   https://arxiv.org/html/2608.00222v1

   Theorems 3.3-3.4: the literal three-dimensional map, determinant, generic
   degree three, and missing cusp. The geometry and the map are prior work.
   The paper attributes the map to Alpöge's announcement.

5. J. S. Milne, Algebraic Number Theory, version 3.08, July 19, 2020.
   https://www.jmilne.org/math/CourseNotes/ANT.pdf

   Theorem 8.31, printed page 147: Chebotarev. Example 8.36, printed page 148:
   cubic factorization types. The corresponding PDF pages were visually inspected.
   Used for the qualitative rational-root gate over Q and number fields.

## Novelty-search scope

Targeted searches included the pairs of coefficient expressions 3BC and 27AC,
Keller-map integral Hasse criteria, and Keller-map T log T counts. No same result
was located in the reviewed primary sources. This is a bounded search, not a
proof that the results have no antecedent anywhere in the literature.

No previous manuscript or third-party font files are copied into the package.
