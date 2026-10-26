# Bounded Pell divisibility: author checkpoint

Author: `circuit_reduction`, 2026-10-26. The new 105-line `BoundedPellDivisibility.lean` and 59-line checks were read completely and compiled freshly, sequentially, under Lean v4.32.0 with `-M6000 -j1` and `Elab.async false`. Both final commands returned zero. The main log is empty; nine axiom reports contain only standard Lean axioms, with no final diagnostics. No frozen source, shared object, umbrella, documentation of the maintained equation, or Git state was changed by this packet.

## Bound and proof

For every `A : Nat` with `1 < A` and positive modulus `m`,

```lean
exists_dvd_yn_le_square (hA : 1 < A) (hm : 0 < m) :
  ∃ k : Nat, 0 < k ∧ k ≤ m^2 ∧ m ∣ Pell.yn hA k
```

The proof maps precisely `Fin (m²+1)` into `ZMod m × ZMod m`. The target has exactly `m²` elements. `Fintype.exists_ne_map_eq_of_card_lt` gives two distinct indices; the proof orders them as `s<t≤m²`. The existing exact Pell subtraction identity gives

`yn(t−s) = xn(s)*yn(t) − xn(t)*yn(s)`

over the integers. Equality of both residue coordinates makes this zero modulo `m`. Thus `k=t−s` is positive and at most `m²`. The exported `residue_pair_collision` and `dvd_yn_sub_of_pair_eq` state these two steps separately.

This is new bounded content. It does not call the old `Diophantine.exists_dvd_yn`, which used an infinite-domain pigeonhole theorem, and does not even import `Common.PellMod`. It assumes no period, orbit enumeration, modular inverse, coprimality, or desired divisible ordinate. The positive-modulus hypothesis is required for the finite target cardinality.

Mathlib's finite pigeonhole theorem is proved using classical metatheoretic infrastructure. This packet gives a finite, explicitly bounded standard-natural argument; it is **not** an HA derivation or a proof that this arithmetic lemma has already been represented in HA. The finite range and bound make a later bounded-search/arithmetic formalization concrete. No `sorry`, new axiom, `native_decide`, or infinite pigeonhole theorem appears in the new sources.

## Exact fresh-seed specialization

For `b,c>0`, `strong_seed` applies the bound to `m=b*c²` and returns positive natural `k,i` with

`k ≤ (b*c²)²`, `yn(A,k)=b*i*c²`, `xn(A,k)>0`, and

`xn(A,k)² − (A²−1)*(b*i*c²)² = 1`

as the literal integer norm. The quotient `i` is positive because `k>0` makes `yn(A,k)>0`; divisibility alone is not used to assume quotient positivity. `strong_seed_at_rank` binds `c` to the actual outer `yn(A,R)` for `R>0`. The checks discharge `R>0` from the actual rank condition `R%4=3`.

This supplies the bounded **first fresh Pell index** used in `ThirteenFreshSeed.auxiliary_exists`. The frozen construction then defines `f=xn(A,k)`, `S=(A²−1)*yn(A,k)`, and uses the already fixed outer index `R` for its secondary auxiliary Pell pair. Its remaining `T` and `m` are obtained through proved divisibility and explicit quotient/carrier formulas. The new lemma can replace the former unbounded first-seed selection; it does not require compatibility with an old private seed. The frozen construction has not been edited, and this packet does not yet package a bound on every final private coordinate or an object-language theorem about those coordinates.

## Checks and dependency scope

The checks cover modulus one (the bound forces index exactly one), impossibility of a positive-index witness for modulus zero, the concrete `A=2,m=3,k=3` witness, failure of modulus two at index one, and the concrete strong seed `A=2,b=1,c=2,k=2,i=1`, whose coordinates are `xn=7`, `yn=4`. They also check the actual rank-modulo-four specialization with all casts and coefficient ordering retained.

Only one custom prerequisite is imported: `Diophantine.Common.Pell`. Its entire source was read, and its current source/object pair exactly matches the previously accepted pair pinned by `object-current-equation2011-dependency-replay.json`. Its private overlay links point to the authenticated existing object; companions are recorded as current observations, not retrospectively claimed historical hashes. Mathlib's existing Pell subtraction and finite pigeonhole APIs were inspected and their sources pinned; the package closure is reused under the matching current toolchain/manifest, not rebuilt. Neither the current215 closure nor `ThirteenFreshSeed` is a compiled prerequisite of this small packet.

Private overlay: `/tmp/bounded-pell-q3lx8lyz`. Exact source/object/command/log pins, prerequisite reuse, and the superseded development diagnostics are in `bounded-pell-divisibility-dependency-replay.json`. There was no broad build or shared-cache overwrite.

## Frozen pins

| Artifact | SHA-256 |
|---|---|
| Main, 105 lines | `4a11cced68e3c38747921c1fb9ed1244669862779e95f7dd7a232ae9aa81e69b` |
| Checks, 59 lines | `6cdc93b9a2cf5294c12a64312a6f43a9f5898380d20c1616f8cc795f424e2ba3` |
| Fresh main object | `a846c93bf531eee33c48e32cc53a7f47795c238214c831facc6ed8be40eaeef2` |
| Fresh checks object | `1264369dfa4e00acce71f8e8a4488b56dab804b0034fdefaf19b8ae0b2a94759` |

This is an author checkpoint; independent review remains separate.
