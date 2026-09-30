# Provenance and theorem boundary

## Repository pin

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `e18718e837d43e162252f9a314e8cb797fbd1a1f`  
Recorded commit timestamp: 2026-09-30 19:50:53 UTC.  
Inspection and manuscript date: 2026-09-30.

The GitHub connector was used to read repository material and commit
metadata. The repository was not modified. Claims about the snapshot are
not claims about any later default-branch state.

The directly relevant inspected materials were:

1. Root `README.md`: repository map and stated theorem boundaries.
2. `Computability/HilbertTenthProblem/README.md`: project scope.
3. `Computability/HilbertTenthProblem/Lean/MRDP.md`: exact MRDP interface,
   proof structure, natural witnesses, and quantitative non-claims.
4. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/README.md`:
   related report's contents and formal-status boundary.
5. Commit metadata at the pin: the merged report and its source descriptions.

The report's distinction from prior work is based on this relevant inspected
material, not on an exhaustive all-file audit. No Lean or Rocq build was run.
The guide says the MRDP theorem has been audited; that statement is attributed
to the repository and is not a new build receipt from this work.

## Primary literature

- David Gamarnik (2007), *On the Undecidability of Computing Stationary
  Distributions and Large Deviation Rates for Constrained Random Walks*,
  Mathematics of Operations Research 32(2), 257–265.
  https://doi.org/10.1287/moor.1060.0247
  Prior exact-stationary undecidability with a Lyapunov certificate. Its
  homogeneous constrained-walk input model is different from this article's
  programmable one-dimensional environments.

- Charles H. Bennett (1973), *Logical Reversibility of Computation*, IBM J.
  Res. Dev. 17, 525–532.
  https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html
  Classical history-recording background. The actual tag map used here is
  specified and proved in the manuscript.

- Kenichi Morita (1996), *Universality of a reversible two-counter machine*,
  Theoretical Computer Science 168(2), 303–320.
  https://doi.org/10.1016/S0304-3975(96)00081-3

- Andrej Dudenhefner (2022), *Certified Decision Procedures for Two-Counter
  Machines*, LIPIcs 228, 16:1–16:18.
  https://doi.org/10.4230/LIPIcs.FSCD.2022.16
  Universality background and the importance of exact instruction-set
  restrictions. Our history register has guarded affine multiplication;
  this is not a new minimal reversible two-counter claim.

- John E. Hutchinson (1981), *Fractals and Self Similarity*, Indiana Univ.
  Math. J. 30, 713–747. Author's retyped paper:
  https://maths-people.anu.edu.au/~john/Assets/Research%20Papers/fractals_self-similarity.pdf
  The separated self-similar dimension principle; a direct proof is included
  for the particular two contractions in the manuscript.

- Joseph Liouville (1851), *Sur des classes très-étendues de quantités dont
  la valeur n'est ni algébrique, ni même réductible à des irrationnelles
  algébriques*, J. math. pures appl., series 1, 16, 133–142.
  https://www.numdam.org/item/JMPA_1851_1_16__133_0.pdf
  Historical source of the elementary approximation obstruction. The needed
  integer-polynomial/mean-value argument is included in Appendix B.

- Boris Adamczewski and Yann Bugeaud (2007), *On the complexity of algebraic
  numbers I. Expansions in integer bases*, Annals of Mathematics 165, 547–565.
  https://doi.org/10.4007/annals.2007.165.547
  PDF: https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf
  Theorem 1, printed p. 549 (PDF index 2), was inspected in the page image:
  algebraic irrational expansions have liminf p(n)/n = infinity. This is a
  deep imported theorem, not established by the finite code or reproved here.

- David Aldous and James Allen Fill (2002; recompiled 2014), *Reversible
  Markov Chains and Random Walks on Graphs*, unfinished monograph.
  https://www.stat.berkeley.edu/users/aldous/RWG/book.html
  Reversible-chain and spectral background; the quantitative bound used
  here is given a direct weighted-convolution proof.

## Claims and non-claims

The paper proposes an explicit combined construction and proves its stated
results mathematically. It does not certify historical priority or claim
that general stationary-distribution undecidability is new. It does not
solve an unrestricted finite-fold or single-fold MRDP problem, prove the
absence of algebraic irrational points in the entire equilibrium Cantor
set, or establish an irrationality exponent for the Thue–Morse equilibrium.

Uniform mixing is from the root, not from every state. The local counter
system is irreducible only on the initialized trajectory component. Finite
certificate witness counts exclude the environment evaluator. The horizon
is external to the polynomial compiler. Countably infinite effective
systems are used; no finite-state Markov universality is asserted.

The tests validate finite instances, formulas, code paths and symbolic
expansions. They do not validate infinite-state theorems, a universal
machine implementation, arithmetical-hierarchy separations, or transcendence.
