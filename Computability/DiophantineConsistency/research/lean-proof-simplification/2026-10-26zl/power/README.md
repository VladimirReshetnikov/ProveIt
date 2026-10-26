# Exact-order client simplifications

**Result:** two independent full-file candidate patches remove **21 physical
lines / 20 nonblank lines**, including all helper costs. No helper is added;
one private, single-use modulus-transport theorem is removed. Every public
theorem signature, definition, computational datum and non-target source byte
is unchanged.

**Validation status:** all proposed Lean is **uncompiled**. Read-only Python
static/finite auditors passed both normal and `-O` execution. Neither those
auditors nor the mathematical review establish Lean elaboration or kernel
acceptance. No upstream source edit, repository fetch, installation, Lean invocation,
or incoming-package script execution was performed. The only remote API read
was an official pinned Mathlib source read; an earlier web read returned a
cache miss, not a policy denial.

## Source and artifacts

- Project pin: `9f35798db4a63c25e435fca14d75931144657d7e`.
- Source subtree: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.
- `source/`: exact pinned reference files for the four reviewed modules.
- `proposed/`: complete candidate files, not isolated snippets.
- `patches/`: independent exact unified diffs, each based on the pin.
- `manifest.json`: complete before/after hashes and full-file costs.
- `evidence/target_accounting.json`: declaration-span counts.
- `evidence/mathlib_order_api.json`: read-only official API excerpts and blob ID.
- `verify_power.py`: read-only static and finite checker, no imports outside the
  Python standard library; prints JSON and does not write or execute subprocesses.
- `verification.json`, `verification_optimized.json`: matching successful receipts.

Run from any directory:

```sh
python3 /path/to/power/verify_power.py --upstream /path/to/pinned/upstream
python3 -O /path/to/power/verify_power.py --upstream /path/to/pinned/upstream
```

Omit `--upstream` to replay against the bundled, hashed source snapshots.

## P1. Reuse the exact order at its actual new clients

`patches/exact_order_clients.patch` changes only
`CurrentPowerCoordinates2011.lean`.

### Direct CRT image, without a second mapped-pair witness

The existing `order_product` proves the order of the actual natural generator
power modulo `a*b` by transporting through `ZMod.chineseRemainder hab`.
Its explicit intermediate equality `hm` is unnecessary: the final step of the
order calculation rewrites the mapped power and natural cast directly, then
uses `Prod.orderOf_mk`.

The complete replacement retains the original statement:

```lean
  calc
    _ = orderOf (ZMod.chineseRemainder hab ((x : ZMod (a*b))^k)) :=
      ((ZMod.chineseRemainder hab).toMulEquiv.orderOf_eq _).symm
    _ = _ := by rw [map_pow, map_natCast]; exact Prod.orderOf_mk
```

This is an exact new-client proof deletion, not a new CRT or order API.
The pinned APIs used are [Mathlib's order preservation and product order](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/GroupTheory/OrderOfElement.lean).
They already occur in the maintained proof. Product natural casts and powers
have the same componentwise definitional behavior used by its old `hm` proof.

**Scope retained:** arbitrary natural `a,b,x,k`; only `a.Coprime b` is required.
In particular `(a,b)=(0,1)` and `(1,0)` are not discarded, modulus one is not
treated as nontrivial, and no unit hypothesis is added. Order zero continues to
mean no positive return to one. The CRT statement is a monoid statement, not
an invalid appeal to a finite group of all residues.

### Order-one corollaries are the zero-level exact-order theorems

`generator_cast_auxiliary` now applies `orderOf_eq_one_iff.mp`, then specializes
the already imported `generator_order_succ` at zero. The simplification list
is only `zero_add`, `pow_one`, and `pow_zero`. Thus the modulus becomes the
actual auxiliary prime and its exact order becomes one.

`generator_cast_C0` does the same with `full_order 0`. Its old proof repeated
the CRT calculation already embodied by `full_order`. There is no dependency
cycle: `full_order` uses `generator_cast_fixed` and `generator_order_succ`, not
`generator_cast_C0` or `generator_cast_auxiliary`.

The first change depends on the already proved exact-order theorem rather than
the weaker modular-residue theorem. Both are already in the imported module;
this is proof reuse, not removal of prime, oddness or first-lift obligations.
No speedup claim is made.

### Eliminate the single-use modulus transport, counting the deletion

`block_order` becomes

```lean
  simpa only [modulus_factorization] using full_order k
```

Its theorem statement is unchanged. The rewrite is only
`(d*auxiliary)*auxiliary^k = d*auxiliary^(k+1)`. The private four-line
`order_transport` declaration, its explanatory comment and one separating
blank line are deleted. `B` remains locally irreducible, and the simplifier
is given no expansion of `B` or the actual physical kernel.

**Lean adoption risk to check:** elaboration of the direct CRT final step and
the dependent `ZMod` modulus rewrite. These are standard definitional/rewriting
steps, but this task explicitly prohibited invoking Lean to certify them.

### Complete accounting

| Declaration | Old lines | New lines |
|---|---:|---:|
| `order_product` | 12 | 7 |
| `generator_cast_auxiliary` | 4 | 3 |
| `generator_cast_C0` | 5 | 3 |
| private `order_transport` | 4 | 0 |
| `block_order` | 3 | 3 |

The private helper's comment and separator account for a further two physical
lines (one nonblank). Whole file: **105→91 physical**, **87→74 nonblank**.
No extra imports, helper modules, adapters or declarations are hidden elsewhere.

## P2. Fuse the guarded cast equivalence instead of proving each direction

`patches/guarded_power_cast_fusion.patch` changes only the proof body of
`PrimePowerOrder.pow_cast_eq_one_iff`:

```lean
  rw [← CharP.cast_eq_zero_iff (ZMod m) m (g^k-1),
    Nat.cast_sub (one_le_pow₀ hg), Nat.cast_pow, Nat.cast_one, sub_eq_zero]
```

This is the same cast-to-zero equivalence already used separately in both
directions of the original proof. Rewriting the divisibility side once yields
`((g^k-1 : ℕ) : ZMod m)=0`; the retained lower bound `one_le_pow₀ hg`
legitimizes casting natural subtraction. Cast normalization and
`sub_eq_zero` then identify the two sides of the iff.

The signature still has **`hg : 1 ≤ g`** and arbitrary `m,k : ℕ`.
In particular `m=0`, `m=1`, `g=1`, and `k=0` remain supported. The guard cannot
be silently removed: for `g=0,k=1,m=2`, natural `g^k-1` truncates to zero and
is divisible by two, but the residue power is zero, not one.

This is a modest **secondary** exact-client cleanup, not novel cast machinery.
It preserves the original API footprint and adds no helper. Declaration
**11→4** lines; whole file **80→73 physical**, **71→64 nonblank**.

## Exclusions and non-candidates

The assumed-applied baseline includes all placed/incoming proposals and the
round-four delivery, through the final bounded cutoff
`91dce223cda86c0755b8a9b2504f84be04443fce`. In particular the old cyclic residue/aligned-coordinate
API (E17), generic cast normalization (LE24), and finite injective-to-surjective
construction (LE04) are not claimed again. Late packet zd additionally excludes
finite `primeFactors` certificates for exact orders and their proposed further
controller-constant clients. The present patches do not generate such a
certificate: they simplify downstream CRT/zero-level consumers of order theorems
already proved in the maintained source. See `LATE_BOUNDARY_REVIEW.md` for the
full fresh zc/zd comparison and the preserved exact residual distinctions.

- `ControllerPowerCoordinates` is unchanged: replacing its finite-bijection
  packaging or restating `ControllerResidueLift.exists_coordinate` would repeat
  already-assumed interfaces. Its actual chosen coordinate witnesses and
  orientation of the equivalence remain untouched.
- `CurrentAuxiliaryOrder2011` is unchanged: all actual residue, divisibility,
  non-square and LTE certificates remain as supplied by the source. Their
  repository comments claiming prior kernel checking are not new validation.
- No generic prime-power order lemma, new CRT interface, weakened oddness
  assumption, residue-only order assertion, or enumerated affine coordinate
  map is proposed.
- Merely deleting intermediate names in `exact_lift` was not delivered as a
  separate idea or credited saving.

## Evidence and boundaries

The auditor checks exact source/candidate hashes, exact whole-file unified
diffs, identical public theorem statements, and byte-identical non-target
content. It rejects proof escapes, checks the retained subtraction guard and
`B` irreducibility, and verifies both zero-level specializations and complete
private-helper removal. Checks use explicit exceptions, not Python `assert`,
so `-O` does not disable them.

Finite regressions cover:

- 27,885 guarded cast cases, including zero modulus and zero exponent;
- the explicit omitted-guard counterexample above;
- 27,265 CRT order cases, including 266 cases with product modulus zero,
  modeled as integer multiplicative order rather than a finite residue ring;
- 144 exact odd-prime-power order cases satisfying both lift hypotheses;
- 512 modulus factorizations, including zero factors;
- the actual modular generator residues modulo `auxiliary²`, `auxiliary`,
  `d*auxiliary`, and `d`, computed by modular exponentiation of two with
  exponent `11360754366`, never by materializing `B`.

The literal first lift is `7300767062`; all three order-one residues are one.
These regressions detect common boundary/numeric errors. They are not universal
proofs and cannot validate Lean tactics, elaboration, typeclass search or kernel
acceptance. The new public statements and their mathematical justifications are
reviewed separately above.
