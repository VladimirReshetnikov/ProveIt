# Source and claim audit

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt

Tree pin returned by the GitHub connector:
`c58206ca101d4744a015a0f0104646109357d943`.

Relevant direct reads:

1. `Computability/HilbertTenthProblem/README.md` (opening relevant range).
2. `Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, explicitly at the pin.
3. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/README.md`.
4. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/10-coherent-circuits-SOURCE_AUDIT.md`, explicitly at the pin.

Code searches were selective. Some search results pointed to older commit
`27e5f69659cd827f758ff6cdbb46030b33e91fa6`; they were used for navigation only.
Neither the whole repository nor its many manuscripts were exhaustively audited.

The prior coherent-circuit work already covers exact finite quantum certificates
and canonical signed representations. The present manuscript credits that
context and changes the object to an infinite-run stopping distribution summarized
by a fixed rational matrix inverse and recurrence. It does not depend on the
repository's unrefereed four-dimensional mortality improvement, universal
operation ledgers, or claimed formalization status beyond the inspected interface.

No Lean build or transitive axiom audit was run. The existing MRDP interface was
read, not independently reverified in this session.

## Primary literature checked

### Eisert–Müller–Gogolin

J. Eisert, M. P. Müller, and C. Gogolin, *Quantum measurement occurrence is
undecidable*, Physical Review Letters 108 (2012), 260501.

- https://arxiv.org/abs/1111.3965
- https://doi.org/10.1103/PhysRevLett.108.260501

Theorem 1 and its surrounding rational Kraus definitions were inspected in the
PDF, including a page image. This is the inherited nine-outcome,
fifteen-dimensional undecidability result. The new geometric-clock wrapper is
proved in full in the article. The package does not instantiate a universal
15-dimensional example; its finite word checks use a small two-outcome test
instrument and establish only implementation sanity for the wrapper identity.

### Liu–Zhou–Barthe–Ying

J. Liu, L. Zhou, G. Barthe, and M. Ying, *Quantum Weakest Preconditions for
Reasoning about Expected Runtimes of Quantum Programs*, extended version, arXiv:1911.12557v3 (2022).

- https://arxiv.org/abs/1911.12557 (version 3 inspected)

Prior work on finite-dimensional quantum expected runtimes, symbolic computation,
and almost-sure/finite-expected-runtime equivalence. The present article does not
claim those facts as new, or claim that previous methods excluded infinite paths.

### Lardizabal

C. F. Lardizabal, *Mean hitting times of quantum Markov chains in terms of
generalized inverses*, arXiv:1907.01313v2, July 9, 2019.

- https://arxiv.org/abs/1907.01313
- https://arxiv.org/html/1907.01313v2

The overview in Section 3 explicitly conjectures rational parameter dependence
for every generalized inverse. The article gives a counterexample to that
*unrestricted* selection quantifier under the AJA=A definition. It does not
refute canonical-inverse rationality, an algorithm restricted to rational
operations, or the source's hitting-time theorems. The corrected canonical
rank-stratum statement is proved by adjugate coefficients. No claim is made
that this interpretation had not previously been noticed or remains a recognized
open problem under a more restrictive intended interpretation.

## What the new package proves

- Uniqueness of the four-equation rational (G,P) interface.
- Peripheral cancellation, stopped CP kernels, and all normalized factorial moments.
- A finite all-moments recurrence and explicit arithmetic circuit.
- Seven-natural-coordinate canonical rational wires and a unique quartic compiler.
- Exact dense-core and generated-example counts, without optimization claims.
- Canonical inverse height bounds and a coarse uniform tail bound.
- Weak-clock resolvent, convergent Laurent coefficients, mixture limit, and inversion.
- Preservation of forbidden legal completed records under a fixed geometric clock.
- A computably scheduled one-dimensional counterexample to a uniform exact-probability graph.
- The elementary unrestricted generalized-inverse rationality counterexample.

Several individual steps are standard mathematics or elementary consequences.
The research contribution is their explicit, fully accounted combination and
its relation to observable-specific Diophantine representations. Historical
priority for the assembled compiler and consequences is not established.

## Limitations

The mathematical manuscript is AI-assisted and unrefereed. No new theorem is
claimed to be formalized in Lean. Physical validity is a promise to the compiler.
The finite recurrence interface is not a single-fold graph in a variable moment
index. The undecidable support family does not have a claimed unique MRDP witness.
No assertion resolves the general single-fold or finite-fold conjectures.

Exact finite tests and the separately implemented checker are implementation
evidence. They do not substitute for the general proofs or for independent
mathematical review. SHA-256 hashes establish package integrity, not correctness.
