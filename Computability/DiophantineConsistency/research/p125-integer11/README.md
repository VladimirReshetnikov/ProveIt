# Package 125: the eleven-integer three-root equations 488/118 and 464/119: iPRA endpoints (closed)

This record documents the iPRA endpoints of two equations in eleven unknowns over ℤ, the paired
three-root norm forms of package 125:

| form | JSON | exact degree | operations |
|---|---|---|---|
| direct | [`integral_direct_paired.json`](../../con-zfc-diophantine-forms/125-unified-binomial-round15/norm/integral_direct_paired.json) | 488 | 118 (74 `mul`, 23 `add`, 21 `sub`) |
| centered | [`integral_centered_paired.json`](../../con-zfc-diophantine-forms/125-unified-binomial-round15/norm/integral_centered_paired.json) | 464 | 119 (74 `mul`, 24 `add`, 21 `sub`) |

On the eleven-integer Pareto row they lie between package 137's 648 / 115 and package 135's
weak-cofactor 398 / 121, and they were the last two points of that row without endpoints. The
package's own proofs are
[`scalar/PROOF.md`](../../con-zfc-diophantine-forms/125-unified-binomial-round15/scalar/PROOF.md)
(the registers and the zero-existence argument) and
[`norm/DEGREE_PROOF.md`](../../con-zfc-diophantine-forms/125-unified-binomial-round15/norm/DEGREE_PROOF.md)
(the norm schedule and the degrees).

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`, each integer unknown written as a difference of two naturals.
The unknowns `j C z h r v w T c n s` and the six ports `beta K0 MC MF cone_A cone_B`
(`P138Ports.ports6`, the source34 tuple) are those of
[package 138](../p138-integer11/README.md).

## The circuit

Nodes 0–123 are common to the two DAGs. The front (the named registers `J` … `Dt`, nodes 20–78)
and the carrier (`K`, `H2`, `H3`, `S`, `zc`, `zc2`, `Ac`, nodes 108–123) are those of package
138's native form, with the index `k = R + 1 + h·X·Y`, gate for gate (`P138Value.regs`). The
back end (`D81` … `Cy`, nodes 82–103, and `S2`, node 113) is new.

`P125Value.back` is the record of the back-end registers, over `P138Value.regsK`:

    I = r·c²;   strong = I·(Delta·I);   Df = 1 + strong;   Q = Delta·strong;   δ = Q − 1;
    b0 = (c − R) + T·(4·I);   V = Df·b0 − c;   shift = Q·V;   Cy = V·shift − 1;
    D81 = 243·Budget − 324;   Dg81 = s·(s·(Dt·D81)) + 81;   P81 = Dt·Dg81;   S2 = S·S.

`P125Value.tail` is the record of the radicands and of the paired norm schedule, over a linear
slot `ζ`:

    Z2 = ζ²;   A = Df·(9·S2);   B = Cy·(δ·S2);   G = P81·S2;
    vnorm = Z2 + A − B − G;   left = Z2·A;   right = B·G;
    ynorm = vnorm² − 4·(left + right);   output = ynorm² − right·(64·left).

The two forms differ only in the slot: `ζ = n·S − Ac` (direct, `P125Value.zD`) and
`ζ = S·(n + Q·V) − Ac` (centered, `P125Value.zC`). The shift `Q·V` does not read `n`, so the
centered value at `n − Q·V` is the direct value at `n` (`valueC_shift`); the shear removes the
top-degree terms of the slot, which lowers the exact degree from 488 to 464 for one more
addition.

In closed form `Df = 1 + Δ·I²`, `Q = Δ²·I²`, `Cy = Q·V² − 1`, and with
`Dg = 1 + (3·Budget − 4)·Dt·s²` the radicands are `A = (3S)²·Df`, `B = S²·(δ·Cy)`,
`G = (9S)²·(Dt·Dg)`. The output is the three-root norm

    N(ζ; A, B, G) = ((ζ² + A − B − G)² − 4·(A·ζ² + B·G))² − 64·(A·ζ²)·(B·G),

the product of the eight conjugates `ζ ± √A ± √B ± √G` (`ZRowsThreeRoot.norm3`,
`P125Value.out_eq`). It fuses the three square conditions `Df = □`, `δ·Cy = □`, `Dt·Dg = □`
of the scalar system into one equation. The weights `1`, `9` and `81` are what separates the
three radicands at a zero: `Df` and `δ·Cy` are `≡ 1 (mod 3)`, so an equality between two
radicands would, after cancelling common factors, equate a multiple of 3 with a number
`≡ 1 (mod 3)`.

## Route

In every model `V` of `𝗜𝚺₁`, each equation has a zero in the ring of differences `DiffRing V`
iff machine 215 halts internally.

**Soundness** (`P125Fold.sound_direct`, `P125Fold.sound_centered`). Both slots are handled by
one argument over a generic slot `ζ` with `S ∣ ζ + Ac`.

* `ZRows/ThreeRoot`: over the ring of differences, a zero of `norm3 Z x y z` with `Z ≠ 0` and
  pairwise distinct `x`, `y`, `z` makes all three radicands squares (`three_squares`); and if
  the three roots are multiples of `S`, so is `Z` (`dvd_of_norm3_squares`).
* `P125Roots`, residues modulo 3: `Δ ≡ 0`, hence `Df ≡ 1` and `δ·Cy ≡ 1 (mod 3)`.
* Nonvanishing at a zero: `S ≠ 0` (the output at `S = 0` is `ζ⁸`, and `Ac ≠ 0`); the three
  radicands are pairwise distinct (after cancelling `S²`, an equality would read
  `9·Df = δ·Cy`, `Df = 9·Dt·Dg` or `δ·Cy = 81·Dt·Dg`, each with one side `≡ 0` and the other
  `≡ 1 (mod 3)`); `ζ ≠ 0` (the output at `ζ = 0` is the square of
  `S⁴·((9Df − δCy − 81DtDg)² − 324·δCy·DtDg)`, whose inner bracket is `≡ 1 (mod 3)`).
* The three roots (`roots`): `Df`, `δ·Cy` and `Dt·Dg` are squares, and `S ∣ Ac` (`S_dvd_Ac`).
* The guard (`guard`): `Dt` is coprime to `Dg`, so it is a square; a nonpositive `Budget` would
  make the square `Dt·Dg` negative, so `Budget > 0`, hence `c ≠ 0`, `I ≠ 0` and `Q > 1`.
* The descent (`descent`): `Q·V² − (Q − 1)·y² = 1` (`ZRowsStrongFold.adjacent_descent`).
* `ZRows/StrongFold.strong_fold`, applied with `I = r·c²` and no multiplier, and `H ∣ K` give
  `P138Rank.Folded` (`P125Fold.folded_of_zero`); `P138Leaf.halt_of_folded` gives the halt. The
  leaf chain of package 138 is reused unchanged.

**Completeness** (`P125Complete.complete_direct`, `P125Complete.complete_centered`).

* The canonical record of package 138 (`P138Canonical.canonical`) fixes
  `j C z h v w c`.
* The guard Pell pair of package 137 (`P137Complete.guard`):
  `g² = 1 + 4·(3·Budget − 4)·τ²·s²`. The cofactor here has no factor 4, so the coordinate is
  `s ↦ 2s` and `Dt·Dg = (τ·g)²`.
* `interp`: the strong pair over the canonical record, with no point and no multiplier:
  `r`, `f` with `1 + Δ·(r·c²)² = f²`, and for every residue target modulo `2s·r` a value `T`
  and an ordinate `y` with `Q·V² − (Q − 1)·y² = 1`
  (`ZRows/LinearInterpolation.supported_interpolation`).
* Carrier: a root of `(t² + 3)(t³ − 19)` modulo `2s·r` (`ZRowsIntersective19.root`) gives
  `Ac = S·H⁴·e0`. The linear unknown `n = H⁴·e0 + 3·f + (Q − 1)·y + 9·τ·g` makes the direct
  slot `S·(3f + (Q − 1)y + 9τg)`, the sum of the three roots, and `P125Value.out_of_roots`
  closes the norm.
* The centered zero is the direct zero with `n` replaced by `n − Q·V`.

No three-square theorem and no division is used.

## Modules

New modules:

| Module | Lines | Content |
|---|---|---|
| `ZRows/ThreeRoot` | 140 | `norm3`; `norm3_squares`, `norm3_of_roots`; `square_of_norm3`, `three_squares`, `dvd_of_norm3_squares` |
| `P125/P125Value` | 262 | `Back`, `back`, `Tail`, `tail`, `outK`, `zD`, `zC`, `valueD`, `valueC`; register equations by `rfl`; closed forms; `out_eq`, `out_of_roots`, `valueC_shift` |
| `P125/P125Roots` | 257 | residues modulo 3, nonvanishing, `roots`, `S_dvd_Ac`, `guard`, `Q_gt`, `descent` |
| `P125/P125Fold` | 177 | `folded_of_zero`, `sound_direct`, `sound_centered` |
| `P125/P125Complete` | 212 | `interp`, `complete_direct`, `complete_centered` |
| `P125/P125SyntaxDirect` | 504 | the 488/118 literal, generated node for node from the JSON; `evalRing_literal`; `literal_zero_iff` |
| `P125/P125SyntaxCentered` | 507 | the 464/119 literal, likewise |
| `P125/IPRAInteger125` | 146 | `Form488` and `Form464`: `expression`, `bridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` |

Reused unchanged: the front, the port facts, the canonical record and the leaf chain of package
138; the guard Pell pair of package 137; `ZRows/StrongFold`, `ZRows/LinearInterpolation` and
`ZRows/Intersective19`.

The three endpoints of each form say that the native, standard and equality-only iPRA theories
each prove `nativeNoZero (signedSplit expression)` equivalent to
`∼mappedNativeRefutation embedding`, the Foundation ZFC consistency predicate: the equation has
no integer zero iff Con(ZFC). The equality-only theory proves the order-erased form.

Every module was elaborated serially, one target per `lake` call, with no errors. The axiom
reports of the two `bridge` theorems and of the six endpoints are `propext`, `Classical.choice`
and `Quot.sound`.

## Checkers

[`tools/gen_literal125.py`](tools/gen_literal125.py) generates the two syntax modules. With
`--check` it confirms, for each form:

* the JSON's pinned SHA-256, schema, name, domain, variable list, node count, output node,
  operation counts, recorded degrees, `description` and `coefficient_binding`;
* that every named register of the JSON is mapped to exactly one field of `P138Value.regs`
  (front and carrier), of `P125Value.back` (back end) or of `P125Value.tail` (radicands and norm
  schedule), or is the slot `Z`, the inlined node `ell`, or the output;
* that the regeneration is byte-identical and the Lean literal matches the JSON node for node;
* numeric agreement, modulo `2¹²⁷ − 1`, with an independent transcription of the register list
  of `scalar/PROOF.md` and of the norm of `norm/DEGREE_PROOF.md`;
* that ten mutation controls are rejected (child, operation, the literals 19 and 64, variable,
  coefficient, index modulus, linear slot, operand order, output node);

and, across the two forms, that nodes 0–123 are shared and that the centered value at
`n − Q·V` is the direct value at `n`, at 40 random points.

Every named gate of the literals closes by `rfl`, except two front gates where the DAG and
package 138's record associate a product differently and the lemma ends with `show … ; ring`:
`Budget` (the term `eta·(eta·(q2·4))` against `eta·(q2·4·eta)`) and `L` (`k·(Y·E)` against
`E·(Y·k)`).

[`tools/check_ports125.py`](tools/check_ports125.py) binds the six ports. The JSONs'
coefficient leaves are symbolic, and the package does not ship its `norm/coefficients/`
directory in this repository. The package's `MANIFEST_SHA256.json` pins the two JSONs, the
binding and the six payloads by byte count and SHA-256, below `norm/` and again below
`scalar/`. The checker confirms the JSONs' pins and topology, requires the two records to
agree, resolves each coefficient pin to the repository copy that packages 131, 135, 137, 138,
144 and 172 are bound to, and compares the payloads with `P138Ports.ports6` through the
transcription and drift guard of
[`check_ports138.py`](../p138-integer11/tools/check_ports138.py).

Both checkers are finite external evidence that the Lean literals are the published equations;
they are not Lean theorems.

## Remaining

Nothing for these two forms, which are the pair the package's `norm/README.md` selects. The
package's other eleven-integer graphs are not covered here. `norm/integral_direct.json`
(488 / 120), `norm/integral_centered.json` (464 / 121) and
`norm/integral_centered_expandedcut.json` (464 / 136) are other schedules of the same degrees
with more operations, which that README calls research comparisons. The `norm_weak/` pair
(456 / 124 and 416 / 125) is dominated on the row by package 135's 398 / 121.
