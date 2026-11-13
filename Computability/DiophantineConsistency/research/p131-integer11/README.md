# Package 131: the eleven-integer two-root equation 810/112: iPRA endpoints (closed)

This record documents the iPRA endpoints of one equation in eleven unknowns over ℤ: package
131's two-root form
[`two_root11_degree810.json`](../../con-zfc-diophantine-forms/131-shared-pell-caps-round16/scalar/two_root/two_root11_degree810.json),
of exact degree 810 with 112 operations (70 `mul`, 22 `add`, 20 `sub`). On the eleven-integer
Pareto row it lies between package 138's 840 / 108 and package 137's 648 / 115. The package's
own proof is
[`TWO_ROOT_PROOF.md`](../../con-zfc-diophantine-forms/131-shared-pell-caps-round16/scalar/TWO_ROOT_PROOF.md).

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`, each integer unknown written as a difference of two naturals.
The unknowns `j C z h r v w T c n s` and the six ports `beta K0 MC MF cone_A cone_B`
(`P138Ports.ports6`, the source34 tuple) are those of
[package 138](../p138-integer11/README.md).

## The circuit

The front is package 138's short form. DAG nodes 17–84 and 101–120 compute the registers of
`P138Value.regsK` with the short index `k = 1 + R + h·4q⁴` (`P138Value.kS`); the Lean value
module reads them from there and does not restate them.

The back end is new. Against package 138:

| | Package 138 | Package 131 two-root |
|---|---|---|
| strong ordinate | `U = A·r·c²` | `U = r·c²` |
| strong norm | on `BP = P·Dm` | on `P` alone |
| linear slot | `Z = S·n − Ac` | `Z = S·(n + V) − Ac` (reads the strong root) |
| output | one outer square condition | two-root norm |

The output is

    Inner² − 4·δ·Guard·Aux,   Inner = δ·(Z² − Guard) − Aux,
    Guard = S²·P·Df,   Aux = S²·Cy,   δ = Q − 1,   Cy = Q·V² − 1.

It fuses the two square conditions `P·Df = □` and `δ·Cy = □` into one equation: if
`P·Df = G²` and `Cy = δ·y²`, the output is `δ²` times the product of the four conjugates
`Z ± S·G ± S·y`.

## Route

In every model `V` of `𝗜𝚺₁`, the equation has a zero in the ring of differences `DiffRing V`
iff machine 215 halts internally.

**Soundness** (`P131Fold.sound`).

* `P131Roots`: at a zero, `δ`, `Df`, `Cy`, `S` and `Z` are nonzero; `P·Df` and `δ·Cy` are
  squares; `P` and `Df` are positive squares; the auxiliary ordinate is integral and `S ∣ Ac`.
* `ZRows/StrongFold.strong_fold`: the early fold and the main index of the eleven-integer
  circuits, stated over plain variables with no register of any circuit. It is applied with
  `I0 = |r|·c²·p0`.
* `P131Fold.folded_of_zero` gives `P138Rank.Folded`, and `P138Leaf.halt_of_folded` gives the
  halt. The leaf chain of package 138 is reused unchanged.

**Completeness** (`P131Complete.complete`).

* `value_of_roots`: over any commutative ring, if `Z = S·(y + G)`, `P·Df = G²` and
  `Q·V² − (Q − 1)·y² = 1`, the output vanishes.
* `interp`: the supported-modulus interpolation for this back end. The guard root is
  `p0 = τ·g` and the strong ordinate is `I = p0·c²·r`. It exports the common value of the
  register `V`, so the linear unknown `n = H⁴·e0 + y + p0·f − V` is defined without
  circularity.
* The canonical record (`P138Canonical.canonical`), the guard Pell pair (`P138Guard.guard`),
  the root of `(t² + 3)(t³ − 19)` (`ZRowsIntersective19.root`) and the exact quotient
  (`P138Complete.shifted_root`) are those of package 138.
* `value_update`: the short-index value at `h·(3w+1)·(2v+1)` is the native-index value at `h`,
  a polynomial identity; `complete` is `complete_native` substituted.

No three-square theorem and no division is used.

## Modules

| Module | Lines | Content |
|---|---|---|
| `ZRows/StrongFold` | 224 | `delta_of_abs`, `adjacent_descent`, `strong_fold` |
| `P131/P131Value` | 180 | `backK`, `valueK`, `value`; register equations by `rfl`; `value_norm`, `value_norm'` |
| `P131/P131Roots` | 346 | nonvanishing, the two squares, integrality of the auxiliary ordinate |
| `P131/P131Fold` | 184 | `folded_of_zero`, `sound` |
| `P131/P131Complete` | 253 | `value_of_roots`, `value_update`, `interp`, `complete_native`, `complete` |
| `P131/P131Syntax` | 467 | the literal, generated node for node from the JSON; `evalRing_literal`; `literal_zero_iff` |
| `P131/IPRAInteger131` | 84 | `expression`, `bridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` |

The three endpoints say that the native, standard and equality-only iPRA theories each prove
`nativeNoZero (signedSplit expression)` equivalent to `∼mappedNativeRefutation embedding`,
the Foundation ZFC consistency predicate: the equation has no integer zero iff Con(ZFC). The
equality-only theory proves the order-erased form.

Every module was elaborated serially, one target per `lake` call, with no errors. The axiom
reports of `bridge` and of the three endpoints are `propext`, `Classical.choice` and
`Quot.sound`.

## Checkers

[`tools/gen_literal131.py`](tools/gen_literal131.py) generates `P131/P131Syntax.lean`. With
`--check` it confirms:

* the JSON's pinned SHA-256, variable list, node count, output node, operation counts, exact
  degree and `coefficient_binding`;
* that every named register of the JSON is mapped to a field of `P138Value.regsS` (front), a
  field of `P131Value.backK` (back) or is one of four unnamed inline nodes;
* that the regeneration is byte-identical and the Lean literal matches the JSON node for node;
* numeric agreement, modulo `2¹²⁷ − 1`, with an independent transcription of the closed form
  of `TWO_ROOT_PROOF.md` §1;
* the transfer identity mirrored by `P131Complete.value_update`, at 40 random points;
* that nine mutation controls are rejected (child, operation, literal, variable, coefficient,
  index modulus, linear slot, operand order of the output, output node).

All named gates of the literal close by `rfl` except two, where the JSON's operand order
differs from `P138Value.regsK`: node 76 (`L`) and node 84 (`P`), closed by `ring`. The literal
keeps the JSON's order.

[`tools/check_ports131.py`](tools/check_ports131.py) binds the six ports. The JSON's
coefficient leaves are symbolic, and the package does not ship its `scalar/coefficients/`
directory in this repository. Two manifests of the package, `MANIFEST_SHA256.json` and
`scalar/SOURCE_PINS.json`, pin the binding and the six payloads by byte count and SHA-256. The
checker confirms that they agree, resolves each pin to the repository copy that packages 135,
138, 144 and 172 are bound to, compares the raw payloads with the package's
`scalar/COEFFICIENT_RECIPE_CHECK.json`, and compares them with `P138Ports.ports6` through the
transcription and drift guard of
[`check_ports138.py`](../p138-integer11/tools/check_ports138.py).

Both checkers are finite external evidence that the Lean literal is the published equation;
they are not Lean theorems.

## Remaining

Nothing for this form. The package's other eleven-integer equations are not covered here and
are not Pareto points of the row:

* `product11_degree966.json` (966 / 109) and `product11_degree882.json` (882 / 110) have both
  a higher degree and more operations than package 138's 924 / 107 and 840 / 108;
* `two_root_weak/two_root_weak11_degree654.json` (654 / 117) has both a higher degree and more
  operations than package 137's 648 / 115.
