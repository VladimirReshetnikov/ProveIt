# ProveIt audit for a constructive Robin theorem

## Snapshot and scope

Repository: VladimirReshetnikov/ProveIt. Current `main` was resolved through the GitHub plugin to **eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98** (commit timestamp 2026-11-20T00:37:55Z, 19 November in Los Angeles). All following content reads use that immutable commit, not moving main. The search index initially returned the parent 26d3cddb53509845fba7a17e35a863657ded573f; its paths were then fetched at the pinned head. This audit read files and a recursive tree; it did not rerun Lean builds or validate every research-packet argument.

The strongest directly relevant conclusion is that the repository has checked finite arithmetic infrastructure and substantial **uncompiled analytic proof packets**, but I did not locate a completed Robin equivalence proof. Searches for Robin, 5040, Mertens and Schoenfeld must not be turned into a proof that no such file exists. The entire Derivations subtree listing was inspected for relevant modules, and its full README was fetched and searched.

## Trust boundary stated by the repository itself

`Logic/PrimitiveRecursiveArithmetic/README.md` distinguishes:

1. ConciseIPRA: Lean-checked syntax, intuitionistic deduction and bi-interpretation.
2. Derivations: Lean-checked values of `Γ ⊢[PRAAx] φ`.
3. Bridge: Lean-checked transports to/from the Foundation presentation.
4. docs/proofs: 115 delivered research packets, explicitly **not verified as packets**. Only separately integrated particular lemmas are checked.

Immutable source: <https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/README.md>.

The full ROOT README and ENDPOINTS were saved in `sources/proveit`. Repository-reported compiler/axiom audit results are evidence of prior builds, not a build performed in this task.

## Actual object theory and exact transfer endpoint

Source `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean` defines `PR : Nat -> Type` by `zero`, `succ`, `proj`, `comp`, and `prec`. `PTm n` is the term syntax. `PRAAx` has projection/composition/primitive-recursion equations, successor nonzero/injectivity, and induction only for a formula with a proof of `.QF`. `PRA.qfInd` constructs the corresponding deduction. It is intuitionistic natural deduction from the imported Deduction module.

Source `.../NativeBiInterpretation.lean` proves, with proof bodies:

```lean
theorem pra_iff_native {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
  (Γ ⊢[PRAAx] φ) ↔ NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ)
```

This theorem transfers an already constructed object proof. It does not supply the analytic mathematics. A Lean theorem about `Real` or `Complex`, or an assumed `Completed` record, is not an object iPRA proof.

Immutable sources:

- <https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean>

## Reusable checked finite arithmetic

These are appropriate imports for a future Robin implementation; their listed limitations matter.

| Module under Derivations/Lean/IPRADerivations | Exact reusable content | Analytic content still outside the module |
| --- | --- | --- |
| `Analysis/ExponentialTail.lean` | Actual finite-tail numerator recursion. For `N=2B²+2B+p+4`, every finite section `S_k=sum_{j<k} B^(N+j)/(N+j)!` satisfies `S_k<=2^(-p-3)`. Named results include `ratio_inv`, `two_pow_fact`, `first_term`, `exp_tail`. Full source read. | It explicitly does not derive the complex names or strict inequality of the infinite sum. |
| `Analysis/FiniteLogarithm.lean` | Literal PR finite alternating polynomial and independent formal derivative; exact coefficient clearing, cutoff recurrences and geometric differential residual. Full source read. | Analytic name identity and composition with exponential are explicitly open. |
| `AnalyticNumberTheory/Harmonic.lean` | `H_(2^(2t)) >= 1+t` in denominator-cleared form; `quo_anti`, `block`, `dyadic`, `harmonic_dyadic`. Full source read. | No Euler constant approximation theorem is present here. |
| `Analysis/ComplexLogarithmName.lean` | Inventory reports an actual rounded PR4 local logarithm observation, discrepancy bound and comparison to exact finite Taylor samples. | Inventory explicitly leaves analytic identification, derivatives and functional laws separate. Source body not independently read in this audit. |
| `AnalyticNumberTheory/FactorTrace.lean`, `FactorVector.lean` | Inventory reports least-prime-factor trace, bounded termination and exact finite factorization reconstruction. | These supply arithmetic foundations, not Robin's colossally abundant reduction. Source body not independently read here. |
| `AnalyticNumberTheory/DivisorSwap.lean` | Inventory reports `d <-> n/d` reindexing for divisor sums. | Source body not independently read here. |
| `AnalyticNumberTheory/DyadicBandSum.lean` | Finite geometric and weighted-geometric sums and `3+4c+(2c²-1)=2(1+c)²`. | Inventory explicitly says zero counts, logarithm bounds and packet analytic statements are not derived. |
| `Foundations/BoundedSyntax.lean`, `BoundedSyntaxInduction.lean` | Inventory reports Boolean compilation of fixed bounded formulas and QF induction through their bits. | No generic uniform reflection or evaluator for arbitrary PR programs is thereby obtained. |
| `Foundations/MasterCertificate.lean` | Inventory reports explicit reverse-list sequence coding and bounded certificate collection under a bounded-totality premise. | Does not give unrestricted choice, unbounded witness search, or analytic totality. |

For the inventory source use:
<https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/Derivations/README.md>.

Exact useful inventory excerpts are saved separately. Full source copies of the first three modules are saved, including original comments and proof bodies. Their presence in this audit should not be described as successful local compilation.

## Zeta packets and their actual status

### Functional equation

`docs/proofs/analytic-number-theory/zeta_functional_equation_ipra/README.md` describes a 26-page quantitative human proof, finite Fourier/Fejer theta construction, reciprocal gamma, and the regularized zeta identity. It states that the analytic argument has not been formalized/kernel-checked, the two Lean drafts were uncompiled, and the full checker and its correctness derivation were not implemented. Its claimed endpoint is `Prf PRAAx [] (residualSentence compiledCheck)`.

Immutable source:
<https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/zeta_functional_equation_ipra/README.md>.

### General zeta packet

`docs/proofs/analytic-number-theory/zeta_ipra_proof_package/lean/README.md` explicitly marks `.lean` files as uncompiled candidates. It proposes: rational codes, fixed PR function compilation; object finite calculus; Euler-Maclaurin with remainder; regularized zeta; theta/gamma; exact residual correctness; finally `pra_iff_native`. It notes correctly that an ambient `Complex` theorem is insufficient and that the absence of `sorry` does not establish completeness.

Immutable source:
<https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/zeta_ipra_proof_package/lean/README.md>.

### Zero distribution

`docs/proofs/analytic-number-theory/zeta_zeros_ipra_2026-11-15/README.md` claims written proofs of zero counts, PR regular-height construction, contour methods and reciprocal zero-sum tails, plus an exact rational certificate for a simple critical-line zero. Its `verification/STATUS.md` explicitly separates those human arguments and executed finite computation from formalization. It says there was no Lean executable and no analytic internal proof was checked. It does not prove RH.

The full `lean/ObjectTargets.lean` was read. It contains finite data structures, formula constructors, the already-proved transfer wrapper, and a `Completed (p : ProgramContracts)` structure whose fields **ask for** the object proofs of generated contour validity, nonvanishing, trivial zeros, symmetry, contour counting and reciprocal tails. It constructs **no instance** of `Completed`. Thus importing it cannot discharge Robin's analytic obligations.

Immutable sources:

- <https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/zeta_zeros_ipra_2026-11-15/README.md>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/zeta_zeros_ipra_2026-11-15/verification/STATUS.md>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/zeta_zeros_ipra_2026-11-15/lean/ObjectTargets.lean>

## Existing arithmetic RH statement

`NumberTheory/RiemannHypothesis/PAStatement/Research/pa-statement-2026-07-09.md` explicitly chooses the Mertens/Littlewood criterion

    forall q>0, exists C, forall n, |M(n)|^(2q) <= C n^(q+1)

as a first-order PA *statement*. Its objective is statement syntax, not the analytic equivalence proof. It lists standard-model semantics and connection with analytic RH as future work. Its Robin subsection records the 5040 criterion and explains the need for exact exponential/Euler-constant/double-log comparison. This note provides an existing problem map, not a theorem reusable as a proved Robin bridge.

Immutable source:
<https://github.com/VladimirReshetnikov/ProveIt/blob/eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98/NumberTheory/RiemannHypothesis/PAStatement/Research/pa-statement-2026-07-09.md>.

## Recommended report language and integration plan

1. Use the exact `PRAAx` target and fixed-PR-program convention; do not replace object derivability by Lean-provability.
2. Reuse finite arithmetic interfaces for rational intervals, summation and bounded loops; give separate actual derivations or explicit uncompleted obligations for gamma/log/exp semantic identification.
3. Treat upstream zeta arguments as human-level candidate ingredients only until their estimates are independently checked or object proofs built. The user authorizes reuse, not silently upgrading their status.
4. Isolate Robin's RH-dependent sharp estimate and the converse oscillation mechanism as the main missing work if not actually supplied. A generic compiler/transfer wrapper cannot supply these.
5. A full honest endpoint needs an inhabitant of `Prf PRAAx [] robinEquivalenceSentence` for fixed arithmetic definitions, plus semantic adequacy relating the RH encoding and the literal strict Robin inequality. In particular a no-counterexample negative form is not automatically the positive strict inequality formula.
6. Keep reported prior builds and checks performed in the present task separate.

## Saved source evidence

`sources/proveit/manifest.json` records pinned Git blobs and URLs for thirteen saved sources. The repository license is MIT No Attribution and is saved as `sources/proveit/LICENSE`. No GitHub writes were made.
