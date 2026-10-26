# Controller proof cleanup — retained fourth-iteration candidates

**Source pin:** `09d65a93c9df8684c1a226341d6a5120623d1cdb`.
**Status:** two independent, source-exact patch proposals; **Lean not compiled**.
No source checkout was modified. No toolchain was installed, no incoming script
was run, and nothing was pushed.

## Result and full accounting

| Retained patch | Whole file physical lines | Whole file nonblank lines | Net physical / nonblank saving |
|---|---:|---:|---:|
| `controller_coprime_cardinality.patch` | 50 → 44 | 43 → 37 | 6 / 6 |
| `controller_hs_inline.patch` | 184 → 169 | 153 → 139 | 15 / 14 |
| **Total** | **234 → 213** | **196 → 176** | **21 / 20** |

These are **new-client proof cleanups**, not new mathematical abstractions.
Both have zero new helper, declaration, import, namespace, or options overhead.
There are no generated replacement wrappers outside these files. Proposed full
module copies are supplied only to review the exact result of each patch; their
unchanged context is not counted as added implementation.

The first patch replaces `exists_coprime_cardinality`, source lines 27–48:
22 declaration lines become 16. The second removes private `hs_mod_of`, lines
152–160 (9 nonblank lines), and its following blank separator (1 physical line).
The three public wrappers shrink respectively 4→3, 5→3, and 6→4 lines: 5 additional
physical/nonblank lines saved. An existing doc comment becomes an ordinary block
comment after its private declaration is removed; this changes no line count.

All 47 public theorem headers in the two affected files are byte-for-byte
preserved. The only removed declaration is the private helper; all four of its
source name occurrences (definition plus three calls) are confined to this file.

## C1: consume nonvanishing directly as a divisibility fact

Target: `ControllerAuxiliaryChoice.exists_coprime_cardinality`.
The existing proof has already chosen `e`, put
`r = t - (e : ZMod C0) * b`, and established `hr : phi r ≠ 0`.
Replace the ten-line local `hc`/`hnd`/`hpos` block by:

```lean
  have hnd : ¬ p ∣ r.val := by
    rw [← ZMod.natCast_eq_zero_iff,ZMod.natCast_val]
    exact hr
  have hpos : 0 < r.val := Nat.pos_of_ne_zero fun hz => hnd (hz ▸ dvd_zero p)
```

The proof is a direct interface conversion:

1. `ZMod.natCast_eq_zero_iff r.val p` says the cast of `r.val` into
   `ZMod p` is zero iff `p ∣ r.val`.
2. `ZMod.natCast_val` identifies that cast with `ZMod.cast r`. Its source
   `[NeZero C0]` premise is already in the unchanged theorem.
3. `phi` is the existing `ZMod.castHom hdiv (ZMod p)`; its application is
   definitionally `ZMod.cast r`, so the remaining goal is exactly `hr`.
4. Every natural divides zero. Thus `hnd` rules out `r.val = 0`, giving
   strict positivity without a separate contradiction/omega block.

The final existing witness and `hp.coprime_pow_of_not_dvd hnd` are unchanged.
Primality, `p ∣ C0`, nonzero projected Boolean translate, and exponent `n`
(including `n = 0`) are all retained. No field structure or nonzero modulus
instance for `p` is introduced.

**Novelty boundary.** Earlier E17/LE24 broadly discuss cyclic residue and cast
normalization. Packet `2026-10-26p` additionally supplies a specific
`SupportDifference.residue_val` projection normal form. That projection is not
claimed here. This is the different, newly introduced auxiliary-choice client:
remove its manually reconstructed `hc`→zero-cast→divisibility implication and
positivity contradiction, at a net six-line cost reduction even with prior
projection contracts assumed available. There is no new generic helper credit.

## C2: inline the three tiny conditional Hs residue calculations

Target: the three final public wrappers in `CurrentControllerData2011`.
Remove private `hs_mod_of` and give each wrapper the corresponding direct proof:

```lean
  rw [Nat.add_mod (1+B*CurrentKernel2011.K),Nat.add_mod 1,
    Nat.mul_mod B CurrentKernel2011.K,B_mod_47,hK,B_square_mod_47] <;> decide
```

The other two proofs differ only in `B_mod_2011`/`B_square_mod_2011` and
`B_mod_auxiliary`/`B_square_mod_auxiliary`. Full statements and exact proofs are
in `proposed/CurrentControllerData2011.lean` and the standalone patch.

The explicitly supplied first operands restrict each `Nat.add_mod` rewrite to
its intended sum instead of repeatedly expanding an outer remainder. The
`Nat.mul_mod B CurrentKernel2011.K` rewrite exposes exactly the two available
residue certificates. Rewriting by the existing `B_mod_*`, the unchanged `hK`,
and existing `B_square_mod_*` leaves only small numeral arithmetic. `<;> decide`
is harmless when `rw` has already closed the goal and otherwise handles that
small arithmetic remainder.

The already-present boundary

```lean
attribute [local irreducible] CurrentKernel2011.K B
```

is preserved exactly. In particular no `simp [B, CurrentKernel2011.K]`, native
evaluation, full `B` power, or 942-row kernel permutation calculation is added.
The conditional numerical calculations are:

| modulus | known B mod m | **assumed** K mod m | known B² mod m | Hs mod m |
|---:|---:|---:|---:|---:|
| 47 | 37 | 26 | 6 | 29 |
| 2011 | 1283 | 1995 | 1091 | 674 |
| 120199 | 37435 | 114787 | 99283 | 36379 |

These checks **do not establish the actual K residues or complete the
controller/Pcst argument**. All three `hK` assumptions remain visible in the
public theorem headers.

**Novelty boundary.** E11's semantic-cutpoint discipline is assumed, not
reproposed; the existing irreducibility barrier is kept. E22's general helper
organization advice is not counted as a new idea. The concrete new source delta
is removal of this nine-line private helper and the redundant witness naming at
its three newly added clients. Unlike adding a shared helper, the complete
helper cost here is negative and explicitly included.

## Withheld duplicate and untouched modules

An initial `ControllerResidueLift.exists_coordinate` cast-projection cleanup
was **withdrawn**, because packet `2026-10-26p` already contains the exact
`ZMod.castHom_apply` / `ZMod.cast_eq_val` / `ZMod.val_natCast` chain in
`SupportDifference.residue_val`, lines 32–34. Neither its proposed module copy
nor a patch is in this packet. Its five-line saving is excluded from every
retained total. See `rejected.json` for the exact prior source path and hash.

`ControllerIntervalSums`, `ControllerOrbitTransport`, and
`ControllerResidueLift` are untouched: their existing interval construction,
additive scaled-coordinate homomorphism, and quotient lift remain the input
contracts. In particular C0=0 behavior of the separate transport API, T=1
endpoints, representative wrap, injectivity, and cardinality guards are not
weakened or replaced by unguarded representative arithmetic.

## Verification and replay

Run from any directory:

```sh
python /path/to/controller/verify_controller.py --source-root /path/to/pinned/upstream
```

The auditor is read-only: patches are replayed in memory, source files are
never overwritten, and its only output is JSON on stdout. It verifies exact
source and output SHA-256 hashes, hunk context/coordinates, unchanged imports,
options and public theorem headers, helper usage/deletion, disjoint patches,
and exact pinned mathlib evidence. It also rejects six deliberately malformed
patches and detects a changed public premise and a proof mutation. All checks
use explicit exceptions rather than `assert`; ordinary and `python -O` runs
produce identical results.

Finite sanity checks passed:

- 6,084 quotient projection cases (unchanged downstream lift, including T=1).
- 27,000 cardinality/coprimality cases, including exponent zero.
- 2,916 interval cases, including modulus one and cyclic wrapping.
- 14,988 full Boolean-subset residue constructions at small valid parameters.
- 2,197 finite modular-polynomial identities, including Nat's modulus-zero
  convention, plus the three conditional Hs numeric rows above.
- Three guard counterexamples: remove the least-representative bound; replace
  a prime by composite 4; or allow the Boolean translate to vanish.

These finite checks test arithmetic specifications, **not Lean elaboration or
kernel acceptance**. `verification.json` is the current observed result.
No Lean or Lake command was invoked. Pinned mathlib definitions were inspected
read-only at revision `81a5d257c8e410db227a6665ed08f64fea08e997`;
`evidence/Mathlib_Data_ZMod_Basic.lean` is the fetched source snapshot,
`evidence/mathlib_api.json` binds exact declaration excerpts by line range,
SHA-256, source Git blob SHA, and URL.

Remaining acceptance work is to apply each selected patch to an authorized
build copy and compile the affected module/checks and normal aggregate checks
with the declared Lean/mathlib versions. The two specific untested elaboration
points are rewrite inference/definitional reduction in the C1 `hr` conversion,
and the operand-directed rewrite sequence and final small `decide` in C2.
No build-speed or axiom-footprint improvement is claimed.
