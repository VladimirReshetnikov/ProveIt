# ProveIt iPRA audit for the new framework report

Snapshot: `3ee850b4c2d650cf01263823fd5415963747c5d0`, retrieved 2026-11-19.
Repository files were read with the GitHub connector at that commit. The
working source copies below live in `research/audit_cache/`.

## Main conclusion

Do not propose another generic certificate/trace/DAG framework as a new advance.
The repository contains 45 foundations packets, and many of their generic
claims now have actual ordinary `Prf PRAAx` implementations. The most useful
next work is a quantitative producer, a corrected mathematical interface, or
an adapter linking an actual program to a genuine object theorem. The report's
factor-contraction producer and the cluster correction fit that criterion.

The top-level README's inventory is stale: it says 115 packets and 16 geometry
packets. The current docs tree contains 127 packet directories and 28 geometry
packets (other area counts are unchanged). More importantly, historical packet
readmes saying that no Lean was compiled describe the delivered packet, not
the current `Derivations/` implementation.

## Authoritative current status sources

All paths below are relative to `Logic/PrimitiveRecursiveArithmetic/`.

| Source | What it establishes / why it matters |
| --- | --- |
| `README.md` | Defines iPRA and separates checked ConciseIPRA/Derivations/Bridge from delivered research packets. The numeric packet inventory is stale. |
| `Derivations/README.md` | Large current module inventory; ordinary closed endpoints have type `([] : List (Fm PTm 0)) ⊢[PRAAx] φ`. Metatheorems are explicitly distinguished. |
| `Derivations/FIBER-CLAIMS.md` | Most useful exact gap inventory. Defines checked/partial/open and maps every FIBER source claim to actual scope and remaining work. |
| `Derivations/FINITE-DEMAND-CLAIMS.md` | Audits all 17 source theorem environments. Finite norm and determinant constructions have precise partial boundaries. |
| `Derivations/MINKOWSKI-CLAIMS.md` | Separates the checked rational finite-box certificate extractor from unfinished rational-polytope volume/certificate production and represented-real endpoints. |
| `Derivations/GAMMA-CLAIMS.md` | Separates actual finite factor/Taylor names from analytic logarithm, exponential, Gamma and integral identifications; all 62 source-ledger families remain in scope. |
| `UNIFICATION-PLAN.md`, `ENDPOINTS.md`, `DEPENDENCIES.md` | Shared backend, provider and replay rules; `#print axioms` audits metatheory separately from object-theory hypotheses. |

Pinned source URL prefix:
`https://github.com/VladimirReshetnikov/ProveIt/blob/3ee850b4c2d650cf01263823fd5415963747c5d0/Logic/PrimitiveRecursiveArithmetic/`

## What is already checked, according to the current source audits

The audit here does not rerun their builds; these are precise repository
status claims, not fresh local verification.

1. **Fixed bounded syntax and Boolean reflection.**
   `Derivations/Lean/IPRADerivations/Foundations/BoundedSyntax.lean` has
   `BFm n`, actual formula/compile operations, capture-avoiding substitution,
   `compile_correct`, arity-indexed PR symbols, arbitrary-term/context
   reflection, and closed Boolean/program endpoints. The grammar includes
   equality/order, propositional connectives and dependent bounded quantifiers.
   It is a fixed-schema family, not an internal universal evaluator.
2. **Least selection, master certificates, demand closure and finite strategies.**
   `BoundedSelection`, `MasterCertificate`, `DemandClosure`, and
   `StrategyRealization` have actual programs and closed conditional object
   endpoints. Finite demand closure stabilizes at the sum of coordinate caps.
   Strategy correctness is acceptance-implies-formula for the fixed pattern;
   it is not extraction from arbitrary classical proofs.
3. **Trace and realizer composition.**
   `TraceReflection` and `GuardedTrace` are established. `RealizerComposition`
   constructs actual composed demands and masters. `RealizerGraph` covers
   typed primitive/sequential/Boolean/product/projection programs, and actual
   bounded/adaptive variants exist. The entire source compiler language is
   still partial; cyclic graph unrolling and further adapters remain.
4. **Dyadic coherence and finite-net lifting.**
   `Analysis/DyadicCauchy` proves the exact cleared-denominator motion theorem,
   including sealed local certificates. `Foundations/FiniteNet` proves the
   conditional finite-net consumer; it does not construct every needed net,
   modulus, coverage or stability certificate.
5. **Obstruction theorems.**
   `UniversalEvaluatorObstruction` proves the external no-PR-universal-evaluator
   theorem and an object diagonal family. `FiniteUseSignObstruction` proves an
   external finite-query exact-sign obstruction for the stated oracle model.
   These are not unproved generic warnings any longer.

## Concrete difficulties this report can address

### 1. Cluster transport: FIBER G1

Current status: **open quantitative/certificate interface**.
Source claim: `docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/08_algebra.tex`,
theorem “Stable cluster transport”.
Audit: `Derivations/FIBER-CLAIMS.md`, row G1 and “Source issues to settle before
cluster formalization”.

The source's component argument does not justify the claimed `2ε` observation
bound: many short edges may form a long component. The new section
`research/cluster_section.tex` proves two correct results:

- Complete multiplicity covers of one finite occurrence multiset imply Hall
  inequalities, and a bounded augmenting-path program constructs a matching
  of error at most `εA + εB`. Matching is a conclusion, not an input.
- If only component balance is available, sorted rank pairing gives error
  `(vC − 1) δ` in a `vC`-vertex component, at most `(2N − 1) δ` globally.
  A balanced connected rational counterexample has matching distance `14/5`
  while every edge has length at most 1.

The report must preserve the producer boundary: the above does not construct
root-counting certificates for every polynomial from coefficient names.

### 2. Complex labels: FIBER G2

Current status: **source statement requires correction**.
Source/audit paths are the same as G1, row G2.

The audit gives an explicit counterexample for `z² + 1`: arbitrarily small
horizontal shifts of valid boxes around `±i` reverse lexicographic order,
although the root separation is fixed. The new stable-locator theorem uses
fixed rational anchors, one occurrence per anchor, and the guard
`distance(ci,cj) >= 2r + γ`; approximants with error `<= γ/4` have unique
nearest-anchor labels. Cross-precision samples of one label differ by at
most the sum of their errors. This is a valid local replacement, not a global
complex-root order.

### 3. Analytic names and actual producer identification

Current status: **many finite parts checked; actual analytic bridges open**.
Audit: `Derivations/GAMMA-CLAIMS.md`.

Actual finite exponential/logarithm sums and their derivative residuals are
implemented in `Analysis/FiniteExponential` and `Analysis/FiniteLogarithm`.
`LogarithmExponentialCoefficients` proves a Bell/history coefficient recurrence
and vanishing of higher coefficients, but it is not linked to literal finite
composition and then to the named analytic functions with tail bounds.
`GammaCanonicalNames` constructs an actual regular joint-tail name; it does
not identify Gamma by its name. A producer theorem that turns finite residuals
and a verified contraction margin into an actual regular solution name is
useful here, but each analytic identification remains a stated instantiation.

For ODEs, current `Foundations/DiscreteGronwall` and `Foundations/OdeRefinement`
prove the discrete estimate and part of the refinement arithmetic. Their
README rows explicitly retain rational-sample frontends, polynomial bounds,
actual polygon construction/interpolation and complete flow identification
as separate work. Do not present generic Gronwall as the new achievement.

### 4. Finite algebra observations need a correct representation boundary

Current status: **partial; spanning does not imply intrinsic invariants**.
Audit: FIBER G3 and its final source-issues paragraph.
Source: `docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/08_algebra.tex`.

A spanning family can carry many lifts of one multiplication operator.
For example, in `A = Q[x]/(x)`, use `b = (1,1)`. Every matrix
`[[a,b],[-a,-b]]` lifts multiplication by `x = 0`, because each column sums
to zero, but its trace `a-b` is arbitrary. Thus matrix traces and
characteristic polynomials are not intrinsic invariants of the algebra from
spanning alone. A basis/freeness certificate fixes the issue. Without one,
the characteristic polynomial remains a valid presentation-dependent
annihilator of the represented element by Cayley–Hamilton, which is useful
for elimination but a different claim.

Current finite-demand norm infrastructure has actual numerical multiplication
matrices and determinant programs, with precise pending determinant,
nonvanishing, sharp-degree and multiplicity obligations. Avoid confusing a
numerical degree variable with an externally fixed Lean matrix size.

### 5. Deep arithmetic producer boundaries remain deep

Sources:
`docs/proofs/diophantine-number-theory/faltings_ipra/README.md`,
`docs/proofs/diophantine-number-theory/siegel_ipra/paper/05_general_route.tex`,
`docs/proofs/foundations/ipra_categorical_methods/paper/sections/07_obstacles.tex`.

General Faltings and Siegel are not proved by the delivered packets. Complete
finite enumeration still requires a proved height cutoff. A bound on the
number of isomorphism classes does not compute representatives: the categorical
packet already supplies the uniform decidable two-class halting obstruction.
Likewise, the full prime-distribution endpoints retain missing quantitative
constants. A new contract notation alone cannot discharge these producers.

## How to word the report's verification status

“The repository's current audits report checked ordinary-iPRA infrastructure
for reflection, selection, traces, demand closure and several realizer
constructions. This report supplies new human proofs of explicit quantitative
producer and cluster-interface theorems, reference algorithms, and object-level
Lean targets. Its new full object derivations have not been completed.”

Use any stronger local verification claim only for the exact modules actually
compiled in this task. Never infer full iPRA proof status from host Lean
theorems, a `sorry`-free uncompiled file, successful reference tests, or a
conditional certificate-consumer theorem whose premise contains the main
unproved construction.
