# ProveIt source context for Fermat's two-square theorem in iPRA

## Retrieval and scope

Read through the selected GitHub connector on 2026-11-22. Branch `main` was pinned to **65b76a5b8aa87ecad4103c2d287eff5660d3c84c**, commit dated 2026-11-22 21:37:36 UTC. The commit message begins “Split the compact Gamma grid and bound coefficient precision variation.”
Commit: https://github.com/VladimirReshetnikov/ProveIt/commit/65b76a5b8aa87ecad4103c2d287eff5660d3c84c

Only repository files relevant to the iPRA interface and finite arithmetic were inspected; no repository mutation was made, and no compilation was rerun. The repository's own README describes the libraries below as kernel checked. That status is reported from the repository, not newly established by this task.

Root Lean and Mathlib version: **v4.32.0**, from `lean-toolchain` and `lakefile.toml`.
https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/lean-toolchain
https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/lakefile.toml

## Foundation and status conventions

The primary README defines iPRA as first-order intuitionistic logic with equality, one function symbol for every primitive recursive definition with defining equations, successor axioms, and quantifier-free induction. It distinguishes:

- `ConciseIPRA`: checked formalization of several bi-interpretable presentations.
- `IPRADerivations`: actual object-theory derivations of form `[] ⊢[PRAAx] φ`.
- `IPRABridge`: checked transports between this ordinary ConciseIPRA interface and Foundation's standard iPRA.
- `docs/proofs`: filed research packets, generally unverified and not rerun on intake.

Main source: https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/Logic/PrimitiveRecursiveArithmetic/README.md

The bridge README explicitly recommends placing new arithmetic derivations in `IPRADerivations`, using `Prf PRAAx Γ φ` with a common finite variable scope; a closed theorem has scope 0 and empty context.
https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/Logic/PrimitiveRecursiveArithmetic/Bridge/README.md

The ordinary interface namespace is `LeanProofs.ConciseIPRA`; arithmetic helper namespace is `LeanProofs.IPRA`; `PTm n` is a term in scope n and `Fm PTm n` is a formula. The notation `Γ ⊢[PRAAx] φ` abbreviates the object derivation type.

## Useful modules and exact declarations

All following module paths expand under
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/`.

| Module | Relevant declarations | Use in the proposed proof |
| --- | --- | --- |
| `IPRADerivations.Core.Division` | `remF, quoF : PR 2`; `rem`, `quo`; `div_mod`, `euclid_unique`, `div_mod_unique` | Remainders, congruences, centered residues, exact quotient checks. |
| `IPRADerivations.Core.Bezout` | `Bezout.bezout`, coefficient terms `Bezout.cur` | PR extended Euclid and modular inverses. |
| `IPRADerivations.Core.EuclidLemma` | `euclid_lemma_at`, `gcd_prime`, `bezout_at`, `dvd_le` | Prime cancellation and inverse construction. |
| `IPRADerivations.Core.Search` | `Search.mu`, `search_spec`, `search_found`, `search_minimal` | Least bounded witnesses with sentinel at the bound. |
| `IPRADerivations.Core.ClockedDescent` | `ClockedDescent.iterF`, `orb`, `clocked_at`, `clocked` | PR orbit plus QF rank-drop invariant, no least-counterexample principle. |
| `IPRADerivations.Core.Quotient` | `Q`, `Q.exact`, `Q.sound` | Compiles ring identities back to object-theory derivations. |
| `IPRADerivations.Core.IntCertificates` | `zle_of_comb`, `zle_of_comb_two`, `false_of_comb`, `nn_zsq` | Signed-square inequalities, nonnegative slack certificates. |
| `IPRADerivations.Core.Permutation` | `Permutation.prod_perm` | Finite product reindexing; potential Wilson backend. |
| `IPRADerivations.Core.ProdLemmas` | `prod_congr_bounded`, `prod_one`, `prod_const_of` | Finite product facts used for Wilson's argument. |
| `IPRADerivations.Foundations.InvolutionParity` | `involution_even` | Alternative finite involution proof route. |
| `IPRADerivations.Foundations.BoundedFormulas` | `BF`, `fmAt`, `bitAt`, `bf_reflect`, `bf_dec`, `bf_choice`, `bf_least` | Compile bounded arithmetic assertions to PR bits before induction. |
| `IPRADerivations.AnalyticNumberTheory.Primes` | `prime`, `lpf`, `lpf_prime`, `dvd_fact` | Standard prime predicate and bounded factor search. |
| `IPRADerivations.AnalyticNumberTheory.Fermat` | `fermat_at`, `fermat` | Fermat's little theorem only; this is not the two-square theorem. |
| `IPRADerivations.DiophantineNumberTheory.Pell` | `brahmagupta` | Existing signed quadratic product identity; direct two-square specialization or a short fresh ring certificate. |

### Key exact interfaces

```lean
-- IPRADerivations.Core.Division, namespace LeanProofs.IPRA
theorem div_mod (z K' : PTm n) :
    Γ ⊢[PRAAx]
      (z ≐ succ K' * quo z (succ K') + rem z (succ K')) ⋏
      lt (rem z (succ K')) (succ K')

theorem div_mod_unique {z q r K' : PTm n}
    (hz : Γ ⊢[PRAAx] z ≐ succ K' * q + r)
    (hr : Γ ⊢[PRAAx] lt r (succ K')) :
    Γ ⊢[PRAAx] (quo z (succ K') ≐ q) ⋏ (rem z (succ K') ≐ r)

-- IPRADerivations.Core.EuclidLemma, namespace LeanProofs.IPRA
theorem euclid_lemma_at {p a b : PTm n}
    (hp : Γ ⊢[PRAAx] prime p)
    (hab : Γ ⊢[PRAAx] dvd p (a * b)) :
    Γ ⊢[PRAAx] dvd p a ⋎ dvd p b

theorem gcd_prime {p a : PTm n}
    (hp : Γ ⊢[PRAAx] prime p)
    (hna : Γ ⊢[PRAAx] neg (dvd p a)) :
    Γ ⊢[PRAAx] gcd p a ≐ one

-- IPRADerivations.Core.ClockedDescent
-- namespace LeanProofs.IPRA.ClockedDescent
-- P : Fm PTm 1; D r : PTm 1
theorem clocked_at (hP : P.QF)
    (hstep : ([] : List (Fm PTm 1)) ⊢[PRAAx]
      P ⟶ (Pat P D ⋏ lt (inst1 r D) r))
    (s : PTm n) :
    Γ ⊢[PRAAx] neg (Pat P s)
```

The clocked-descent source defines the PR orbit and proves the QF invariant
`P(orb(k,s)) ∧ rank(orb(k,s)) + k ≤ rank(s)`; at the initial rank plus one there is a contradiction. For a constructive terminating state machine, use an analogous guarded invariant or apply this to a bad-state predicate after coding the bounded “no solution” assertion.

### Important primality detail

The existing prime formula is syntactically quantified:

```lean
def prime (p : PTm n) : Fm PTm n :=
  le two p ⋏ Fm.all
    (le two (var 0) ⟶
      lt (var 0) (Syn.shift p) ⟶
      neg (dvd (var 0) (Syn.shift p)))
```

It is a bounded assertion in meaning, but it is not literally `QF`. Do not place it inside the invariant passed to QF induction without first compiling it to a PR characteristic term. Alternatively, retain the prime assumption in the fixed context. `BoundedFormulas.bf_reflect` supplies the relevant bridge between bounded formulas and equations `bitAt A y ≐ one`.

## Object proof versus metatheorem

A Lean theorem about ordinary `Nat`, even if it computes witnesses and uses no classical tactic, does not by itself supply an iPRA derivation. The sought final endpoint is an actual `Prf PRAAx [] φ` with explicit PR terms and first-order formula. Mathlib can be used in the metatheory to compile polynomial identities because `Q.exact` returns a derivation; arbitrary semantic reflection from a true Nat theorem is not available.

For a Foundation endpoint the checked bridge supplies:
- `IPRABridge.conciseToStandard`,
- `IPRABridge.standardToConcise`,
- `conciseProvable_iff`, `standardProvable_iff`.

## Search scope and unimplemented work

The recursively listed `Derivations/Lean` tree has no path named Wilson, TwoSquares, or SumOfSquares. This is only a path-name observation, not a proof that no equivalent theorem is present. The listed `Fermat.lean` was read and is explicitly Fermat's little theorem. The report provides the Wilson half-factorial/root proof, the square-grid extraction, and the optional centered-residue descent separately. Importing the existing repository does not yet produce the new theorem.

## Saved source snapshots

`repo_sources/` contains selected unchanged text snapshots from the pinned commit. They were read through GitHub; their original blob SHA and source URL are recorded in `repo_sources/provenance.json` and `repo_sources/grid_provenance.json`. They are reference sources, not newly compiled dependencies.

## Supplemental: preferred Wilson-plus-grid proof

The primary proof can avoid descent. Use h = isqrt(p), the first p+1 indices of an (h+1)-by-(h+1) grid, and the residue map u + t*v modulo p where t*t = -1 mod p. A collision has a positive squared norm below 2p and divisible by p, hence exactly p.

Two checked source modules directly support this approach.

1. `IPRADerivations.Core.Pairing`, namespace `LeanProofs.IPRA`, defines `isqrtF : PR 1`, with term `isqrt z`. Its recurrence is
   `isqrt 0 = 0`,
   `isqrt (z+1) = isqrt z + eqb((isqrt z+1)^2,z+1)`.
   Theorems `isqrt_le` and `lt_isqrt_succ_sq` provide
   `isqrt(z)^2 ≤ z < (isqrt(z)+1)^2`; `isqrt_unique` supplies uniqueness.
   https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Pairing.lean

2. `IPRADerivations.Core.Pigeonhole`, namespace `LeanProofs.IPRA.Pigeonhole`, defines PR witness terms `phpI S K x` and `phpJ S K x` and proves
   ```lean
   theorem pigeonhole {K x : PTm n}
       (hr : Γ ⊢[PRAAx] Permutation.rangeAll S K x) :
       Γ ⊢[PRAAx]
         lt (phpI S K x) (phpJ S K x) ⋏
           (le (phpJ S K x) K ⋏
             (inst2 S (phpI S K x) x ≐ inst2 S (phpJ S K x) x))
   ```
   Here `S : PTm 2`. `Permutation.rangeAll S K x` means `∀i, S(i,x)<K`, with no range guard on i. For the proposed map, taking the final remainder modulo p makes this hold on all inputs.
   The proof uses bounded occurrence counts and `Core.Search`, not unbounded choice.
   https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Pigeonhole.lean

There is also a small alternative bounded-search square-root module:
`IPRADerivations.Geometry.Hyperbox.SquareRoot` defines `ceilRoot` and proves `ceilRoot_majorizes` and `ceilRoot_minimal`, but the floor-root lemmas in Core.Pairing fit the proof directly and avoid extra geometry imports.
https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Geometry/Hyperbox/SquareRoot.lean

### License

The root `LICENSE` at the pinned commit is the **MIT No Attribution License**, copyright 2026 ProveIt Contributors, permitting use, copying, modification and distribution. The inspected root-project Lean files have no distinct license headers. This supports source reuse; for a source-light research packet, provenance links and a dependency manifest remain sufficient.
https://github.com/VladimirReshetnikov/ProveIt/blob/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/LICENSE


