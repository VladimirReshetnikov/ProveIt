# GammaProver.nb: algorithm analysis and the lattice-reducer rewrite

- Status: Report (analysis of prior art + the replacement implementation)
- Created (UTC): 2026-06-10T19:16:58Z
- Repository HEAD: 54253b86d81cf32f4afc2913f5a126bdfe3f1e65
- Subject notebook: `GammaProver.nb`, in the owner's local notebook corpus
  (local path redacted at the ProveIt intake, 2026-10-07)
  (and its recovered database `GammaRules.wdx`, vendored as
  [`../../identities/harvested-gammaprover-rules.wl`](../../identities/harvested-gammaprover-rules.wl))
- Replacement: [`../../tools/gamma-reducer.wl`](../../tools/gamma-reducer.wl)
- Requested by Vladimir: *"the algorithm … keeps rediscovering the same
  identities repeatedly, and the new ones appear with increasing time
  intervals between them. Please analyze it and try to rewrite it in a more
  efficient way."*

## 1. What GammaProver.nb does

Reconstructed from the notebook source (28 cells; main program one
`Block[{Γ, sin}, Module[…]]` cell):

- **Candidate generation.** An infinite enumeration over pairs `(q, m)`
  (`q` walks the rationals from 1/3 via a successor operator `q⁺` that
  advances to the next coprime numerator / next denominator; `m = 1, 2, 3, …`).
  For each pair, one instance of the **Gauss multiplication theorem** is
  instantiated:
  `Π_{j<m} Γ(q + j/m) = (2π)^((m−1)/2) m^(1/2−mq) Γ(mq)`.
- **Normalization.** Every `Γ` in the instance is normalized into `(0, ½)`
  by `ReduceGamma` (recurrence for arguments outside `(0,1)`, reflection
  `Γ(p) = π/(sin πp · Γ(1−p))` for `p ∈ (½,1)`).
- **Knowledge application.** The accumulated `rules` association is applied;
  if a `Γ` survives, the instance is solved for the **most complex**
  surviving argument (`Precedes` orders by denominator, then numerator) and
  a new rule `Γ(arg) → rhs` is recorded.
- **Simplification.** The elementary side of each new rule goes through
  `FullSimplify` with a custom complexity function and a
  **`TimeConstraint -> {120, 120}`** budget.
- **Bookkeeping.** A `seen` association of processed expressions; a
  `UpdateList` pass that re-applies each new rule across previously stored
  entries; a WDX dump (`rules`, `seen`) every 50 discoveries. The recovered
  database holds 550 rules and 1117 seen entries.

## 2. Why it slows down

The symptom — rediscovery plus ever-longer gaps between new identities —
follows from three structural properties:

1. **Span-membership is discovered only by paying full price.** Whether a
   new `(q, m)` instance carries new information is determined by
   normalizing it, substituting the entire rule base, and simplifying — and
   *most* instances are in the span of the existing rules (each new rule
   makes that more likely). The prover has no cheap test for "this instance
   is dependent", so the duplicate fraction → 1 while the per-candidate
   cost stays high. This is the saturation pathology: work per discovery
   grows roughly like (cost per candidate) / (fraction of candidates still
   novel).
2. **`FullSimplify` (2-minute budget) sits on the hot path.** Every solved
   rule simplifies a growing sin/radical product. As denominators grow,
   the algebraic objects get heavier, so even *successful* discoveries get
   slower — the second half of the symptom.
3. **No completeness notion.** The relation content of a denominator grid is
   finite, but the enumeration cannot see that; it keeps spending candidates
   on exhausted grids. There is no termination condition (`While[True, …]`).

Two smaller compounding costs: the `UpdateList` cascade re-rewrites all
prior entries on each new rule (quadratic-flavored growth), and the `seen`
check happens *after* `ReduceGamma`, so distinct `(q, m)` pairs that
normalize to the same instance still pay the normalization.

## 3. The rewrite: a relation lattice, row-reduced once per grid

The decisive observation: in log-Gamma coordinates everything is **linear
algebra over ℚ**. For the denominator-`N` grid set
`x_k = LogΓ(k/N), k = 1..N−1` (`LogΓ(1) = 0`):

- reflection: `x_k + x_{N−k} = log π − log sin(πk/N)` (k < N/2);
- Gauss, for each divisor `d ≥ 2` of `N` and `k = 1..N/d`:
  `Σ_{j<d} x_{k+jN/d} − [dk<N]·x_{dk} = ((d−1)/2)(log 2 + log π) + (½ − dk/N)·log d`.

All right-hand sides are **exact symbolic logs**; the matrix is small
(`O(N)` rows × `N−1` columns). One `RowReduce` of `[M | I]` over ℚ (columns
ordered numerator-descending so pivots land on large numerators) yields:

- a reduction `Γ(k/N) = exp(elementary) · Π Γ(basis)^{ℚ}` for **every
  non-basis k at once**, with the elementary side computed exactly as
  (combination matrix) · (rhs vector) — no `FullSimplify` anywhere;
- the **basis** — the grid's irreducible Γ-values — and with it a
  *termination guarantee*: the grid is provably exhausted, and the lattice
  rank says exactly how many independent values remain.

By the Koblitz–Ogus theorem the reflection and multiplication relations
generate **all** multiplicative relations among Γ-values at rationals
(modulo algebraic numbers and π-powers), so this is not a heuristic
replacement: relative to that classical result, the lattice output is the
*complete* answer the saturation loop was approximating from below.

The same row-combination matrix is, incidentally, a **multiplier
certificate** in the sense of the Phase-3 proof program
([`../proof-certificates.md`](../proof-certificates.md)): the reducer's
output is born proved, not merely verified.

## 4. Results

Implementation: [`../../tools/gamma-reducer.wl`](../../tools/gamma-reducer.wl)
(`GammaGridReduce`, `GammaGridRules`, `GammaReduce`; every emitted closed
form is re-verified numerically at 40 digits before being returned).

| measurement | lattice reducer | GammaProver.nb |
|---|---|---|
| denominator-120 grid, complete (103 reductions, 16-element basis) | **0.42 s** | (open-ended enumeration) |
| all 151 grids spanned by the recovered database (denominators ≤ 308) | **73 s**, every rule verified | multi-hour sessions, 550 rules, no terminus |
| coverage of the 550 `GammaRules.wdx` arguments | **550/550** | — |
| termination criterion | lattice rank (provable) | none |

Sample rendered output (the sin-values collapse to radicals on their own):

```
Γ(5/12) == 2^(2/3) √π Γ(1/12) / ((1 + √3) Γ(1/6))
```

## 4a. The Python port and the performance comparison

[`../../tools/gamma_reducer.py`](../../tools/gamma_reducer.py) implements the
identical algorithm in pure Python: exact ℚ arithmetic via
`fractions.Fraction`, the elementary right-hand sides carried through the
elimination as sparse atom→coefficient dicts (atoms: `log π`, `log n`,
`log sin(πk/N)`) instead of an identity-block combination matrix, and
mpmath 50-digit verification. Both implementations produce **identical
output** (same rules, same bases — N=12: 9 rules over {Γ(1/12), Γ(1/6)};
N=120: 103 rules over a 16-element basis).

| workload (generation only) | Wolfram (`gamma-reducer.wl`) | Python (`gamma_reducer.py`) |
|---|---:|---:|
| denominator-120 grid (103 rules) | 0.42 s | **0.056 s** |
| all 151 `GammaRules.wdx` grids, ≤ 308 (15 588 rules) | 75.3 s | **7.44 s** |
| mpmath verification of all 15 588 | — | 8.32 s |

Python wins by ~**10×** on this workload as written. The gap is an
implementation artifact, not a language verdict: the Wolfram version
row-reduces the augmented `[M | I]` block (an extra m×m dense identity,
~520×830 total at N=308) and assembles the symbolic elementary sides as a
combination-matrix product, while the Python port eliminates with lean
sparse rhs dicts and no identity block. Porting the rhs-dict trick back to
the Wolfram implementation would likely close much of the difference;
either implementation beats the original saturation prover by **orders of
magnitude** (hours → seconds) with a completeness guarantee.

## 5. Engineering notes

- `SparseArray[{…rules…}]` with a **repeated position takes the first rule,
  not the sum** — the Gauss row where `dk` coincides with a product index
  silently corrupted the matrix until per-entry accumulation replaced the
  rule list. (Caught by the numeric per-row canary; the corrupted lattice
  "proved" Γ(1/3) reducible to Γ(1/12), which the dimension count refuted.)
- `FirstCase[list, p -> _]` parses the second argument as *pattern →
  replacement*, not as a Rule-shaped pattern — use `MemberQ[First /@ list, p]`.
- Auto-memoization on `GammaGridReduce[N]` makes repeated single-value
  queries on one grid free.

## 6. Follow-ups

1. Emit a full mega-store (all grids to some ceiling, e.g. `N ≤ 360`) as an
   `identities/` store, superseding the prover database's coverage.
2. The **polygamma analogue** — **done** (2026-06-10):
   [`../../tools/psi_reducer.py`](../../tools/psi_reducer.py) derives the
   complete trigamma reduction tables (grids 3–100: 3 428 rules, all
   mpmath-verified, 7.7 s; basis dimensions = φ(N)/2), subsuming the
   70-entry `Trigamma.nb` harvest and the `TrigammaSearch.nb`-era PSLQ
   hunting.
3. Plug the row-combination matrix into the Phase-3 certificate store
   format so every grid reduction lands as a replayable certificate.
4. Basis-choice refinement: the current numerator-descending pivot order
   gives small-numerator bases; a `Precedes`-compatible or
   Vidūnas-canonical column order is a drop-in change.
