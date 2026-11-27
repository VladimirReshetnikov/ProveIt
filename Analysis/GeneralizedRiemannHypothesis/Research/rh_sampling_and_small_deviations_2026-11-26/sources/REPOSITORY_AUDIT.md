# Source audit: lsernau/grh-lean

Audit date: 26 November 2026. Repository commit: `72fead102f663d5c7a407964a13dc0cf9d977207`, committed 2026-11-25T20:38:07Z. Tree: `5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f`. All fetched source snapshots are pinned to this commit. Metadata and blob hashes are in `repository_metadata.json`.

## Scope and trust boundary

This is a source-reading audit of selected public files. No Lean build or independent kernel replay was performed in this audit. The repository's README reports that every source file compiles without `sorry`, that its five exported theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`, and that independent checkers nanoda, con-leche, and con-ron accept their dependency export. Those are **upstream-reported checks**, not checks repeated here. A `Challenge.lean` containing `sorry` is reported as an intentionally unbuilt comparator target.

The root README states that the proof has received machine checks but has not been read through by a mathematician and that no accompanying paper exists. The source describes the proof as Levent Alpöge's with Claude and the rewrite as an Anthropic collaboration.

The exact exported scope is **RH and Dirichlet GRH**, for every positive modulus and every Dirichlet character, including imprimitive characters. It does not by itself establish GRH for arbitrary Artin, automorphic, or number-field L-functions.

## The five statements

`grh/src/Statements.lean` imports Mathlib alone and fixes four propositions; `grh/src/Main.lean` exports these five theorems:

1. `riemannHypothesis : RiemannHypothesis` (Main line 5).
2. `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine` (line 8): if ζ(s)=0, s is not -2,-4,..., and s≠1, then Re(s)=1/2.
3. `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` (line 13): for N≥1 and χ mod N, Re(s)>1/2 and (χ≠1 or s≠1) imply L(s,χ)≠0.
4. `LFunction_eq_zero_re : DirichletLZerosOnLine` (line 17): every zero with 0<Re(s)<1 has Re(s)=1/2.
5. `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine` (line 21): primitive-character special case.

The point s=1 is explicitly excepted in the nonvanishing formulation because it is a pole for the principal character. The Dirichlet statements do not describe zeros with Re(s)≤0.

The configured versions are Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (README). The recursive source tree contains 803 Lean files under readable `grh/src` and 794 under compact `grh-compact/src`. The README estimates 300,000 lines of readable code / 76,000 compact code lines and one to two hours on 12 cores with 24 GB memory.

## Mathematical architecture

The three structural inputs are:

- **A, short integral forms:** span the source by small integral forms and bound the denominators/index of normalized Poincaré images.
- **B, enough forms:** translates of these images span almost all of a target space, using a second-moment argument.
- **C, integral forms are long:** theta-lift determinants and a product formula give a lower bound for the same covolume corrected by index.

Write D for the target dimension, n for the independent family size, V for log squared covolume, δ for an index bound, H for the shared main term, m for the number of lifts, and R for a weighted prime remainder. Up to explicit errors the comparison is
    H ≤ (V+2δ)/D ≤ H - (n/D)mR.
The leading H cancels. The actual `star_inequality` in `New/Reduction/MainInequality.lean`, line 91, is
    m · totalRemainder ≤ f · a · (log b)^5.
The index enters twice. A family of at least half the target dimension is enough.

The construction uses a CM field K(ζ), theta lifts between unitary spaces, local divisibility of derivatives of theta functions, integral lattices, and anticyclotomic twisting to control denominator losses. It is not a short elementary proof disguised by the final five export declarations.

## Most directly reusable analytic idea

For a prime d and positive q, define
    λ_{q,d}(n) = 1_{n≡1 mod q} Λ(n)(1-(n/d)),
    R_{q,d}(x) = Σ_{n≤x} λ_{q,d}(n)(1/n-1/x) - log(x)/φ(q) - c_{q,d},
where c is the constant making R tend to zero. The weight λ is nonnegative. These definitions and the transform identity occur in `New/Reduction/Zeros/PrimeError.lean`.

Let entireLχ be Lχ with its principal pole removed. For v↦R(e^v), the transform
    ∫_0^∞ R(e^v)e^{(1-s)v} dv
is meromorphic with at most simple poles in Re(s)>0. Away from s=1 its residue is
    [Σχ ord_s(entireLχ) - Σχ ord_s(entireL(χχ_d))]
    / [φ(q)s(1-s)].

The criterion `New.LFunction_ne_zero_of_primeRemainder_le` (Criterion.lean, line 37) says: if q is a positive multiple of 8, d0≡7 mod 8 is coprime to q, β>1/2, and for **every prime d≡d0 mod q**
    R_{q,d}(x) ≤ x^{β-1}
eventually, then every Dirichlet Lχ mod q is nonzero at every ρ≠1 with Re(ρ)>β.

The quantifier over d matters. For a putative zero ρ, a quadratic-twist selection theorem chooses one d for which all twisted L-functions are zero-free in a finite rectangle reaching the height |Imρ|. The residue difference then becomes a sum of nonnegative untwisted multiplicities. At real x in (β,1), x(1-x)>0; at real x≥1 no zero contributes. Landau's lemma converts the eventual **upper** bound alone into vanishing of every pole to the right of β, a contradiction.

`Lib/Analytic/Landau.lean`, line 217, exposes the reusable theorem:
if E is polar, E(v)≤exp((β-1)v) eventually, and all real residues to the right of β have nonnegative real part, then every residue at Re(ρ)>β vanishes. This is explicitly attributed there to classical Landau/Widder/Montgomery–Vaughan theory. The novelty of a follow-on result must therefore lie in a new condition/application, not in relabeling Landau's lemma.

The final source bound (OneSidedBound.lean, line 125), for 0<ε<1/100, is
    R_{q,d}(x) ≤ (64φ(q)+3)x^{-1/2+6ε}
for large integers x. Interpolation and shrinking ε give the needed real-variable bounds. The scale m is in [√x,2√x], while log b is at most 2x^ε.

## Other reusable structural idea

`New/Reduction/Lattices/Heights.lean` allows a different family member y_ι, hence a different twist, at each prime/p-adic embedding ι. A **single common multiplier H** controls all members simultaneously. Products add height budgets. The product formula says that the constant family 1 cannot have negative height. This separates local choices while retaining one global arithmetic obstruction. It is potentially useful in determinant methods where one universal twist is impossible.

The folder name `New` is not a novelty certification: GUIDE explicitly says folder/name assignments are a working classification and make no claim of novelty.

## Pinned citation URLs

- Root and status: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/README.md
- Scope/checks: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md
- Statements: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean
- Exports: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean
- Guide: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md
- Main comparison: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean
- One-sided criterion: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean
- Prime transform: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/PrimeError.lean
- Landau lemma: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Landau.lean
- Heights: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/Heights.lean

## Snapshot license

The unmodified repository excerpts are Apache-2.0. A copy of upstream LICENSE, grh/NOTICE, and grh/ATTRIBUTION.md accompanies the snapshot. This is a small review snapshot, not a complete buildable copy of the repository.

