# Exact arithmetic conditions for a guarded same-q/k target

This is an ordinary-integer characterization, not yet a Lean theorem or an internal-model result. Let q≥3 and let G be any integer. Write `g0=G mod q⁴` for its unique residue in `[0,q⁴)`. We seek integers F′,C′ with

```
F′≥1, C′≥1, F′+C′<q,
q⁴ ∣ q(q−F′)−C′−G.
```

Such a pair exists **if and only if**

```
2q−1 ≤ g0 ≤ q²−q−1,
L := q²−g0,  F′ := L div q,  C′ := L mod q,
F′≥1, C′≥1, F′+C′<q.
```

When it exists, the pair is unique. Indeed, a guarded pair has `L=qF′+C′` and `q+1≤L≤(q−1)²`, so its `G′=q²−L` lies in `[2q−1,q²−q−1]`, strictly below q⁴. The congruence therefore forces `G′=g0`. Conversely, the stated digit inequalities give the pair and `q(q−F′)−C′=g0`. Ordinary quotient/remainder uniqueness proves uniqueness. The finite diagnostic checks this criterion exhaustively for q=3,…,12, including negative integer representatives; the proof for arbitrary q is the preceding arithmetic argument, not the enumeration.

For an actual positive 74 zero with the same J and k as a proposed target, let `RJ=(MC+qMF)J` and `R=(q²−1)G+RJ`. The checked offset theorem gives `q⁴ | k−R−1`. Since

```
(q²−1)·(−1−q²) = 1−q⁴,
```

the canonical residue is fixed by

```
g0 = [−(1+q²)(k−1−RJ)] mod q⁴.
```

A guarded target that remains a 74 zero with this q,k must therefore use the unique pair above, if the triangular test succeeds. The current full-graph facts have not been shown to force that test; the audited F/C remainder fixes only the lower q² residue and does not by itself establish the required q⁴ target or triangle. This is a necessary arithmetic test for an arbitrary same-q/k target, not a claim that such a target exists.

For the narrower audited **exact-V/Z gauge**, keep J,i,w,s,eta,zeta fixed, so c,f,h,D,H,K,Q,M,Gn are unchanged. Assume the source zero has its graph-derived c>0, f>0, h>0, D>0, H>0; let L₀=V² and N be the positive carrier variable. For the unique target F′,C′, calculate `ΔR=R′−R`, `ΔB=B′−B`. There is an integer choice of T′,N′ preserving V and Z exactly and making all target coordinates positive **if and only if**

```
c ∣ ΔR,
hD ∣ D·ΔB − h·ΔR,
T′ = T + ΔR/c > 0,
N′ = N + L₀·ΔB + (D·ΔB−h·ΔR)/(hD) > 0.
```

The quotients are exact signed integer quotients. Necessity follows by subtracting V and Z and canceling the nonzero factors f and H; sufficiency follows by substitution in the checked conditional 74 DAG gauge and positivity of the unchanged coordinates and guarded pair. This is an iff for the **specified exact-V/Z, fixed-coordinate integer gauge**, not for all possible zero-preserving transformations: sign-flipping V or Z, changing J/k or other fixed coordinates, or transformations not preserving these registers remain open. The offset, gauge and parent output objects retain their documented direct-provider and source-binding limitations. No full graph equivalence or iPRA result is asserted.

Run `python3 -I -S -B research/trace74-guarded-gauge-characterization/check.py` from `Computability/DiophantineConsistency`. Author exit 0, checker SHA-256 `9084e9ea94959627f6dbefb1f8d47706f1dd2876e0863bec1b6ee948d34f35ca`, stdout SHA-256 `1f2a927607c4b9bc50a7a63f2b08ee521f903476494c104fd668b715fce0268e`, stderr empty. The source-pinned checker is a finite diagnostic; it is not a Lean proof of this characterization or fixed-port binding.

Independent [mathematical and diagnostic review](../../reviews/trace74-guarded-gauge-characterization-independent/README.md) passed, SHA-256 `2badd530b87c193634b2a2835794f502ccd0fe72d882f7da3c6e2340776b6c6a`. It checked the arithmetic ranges, inverse and exact fixed-coordinate V/Z iff; it does not establish internal-model transfer or gauge solvability.
