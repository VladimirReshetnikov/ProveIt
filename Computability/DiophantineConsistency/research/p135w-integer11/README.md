# Package 135: the eleven-integer weak cofactor equation 398/121: iPRA endpoints (closed)

This record documents the iPRA endpoints of one equation in eleven unknowns over ℤ: package
135's weak-scale direct form
[`weak_cofactor11_none.json`](../../con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/weak_cofactor11_none.json),
of exact degree 398 with 121 operations (77 `mul`, 24 `add`, 20 `sub`). On the eleven-integer
Pareto row it lies between package 125's 464 / 119 and package 135's free-scale 352 / 125. The
package's own proof is
[`PROOF.md`](../../con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/PROOF.md).

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`, each integer unknown written as a difference of two naturals.
The unknowns `j C z h r v w T c n s` and the six ports `beta K0 MC MF cone_A cone_B`
(`P138Ports.ports6`, the source34 tuple) are those of
[package 138](../p138-integer11/README.md).

The three free-scale forms of the same package (352 / 125, 340 / 129, 328 / 130) are recorded
in [`p135-integer11`](../p135-integer11/README.md). This form has a different front, so it has
a route of its own.

## The circuit

The circuit is a splice of two circuits that already have Lean routes:

| part | DAG nodes | shared with |
|---|---|---|
| front and carrier | 18–75, 81–82, 100–130 | package 137's weak product form, node for node (`P137Front.front`) |
| back end | 76–80, 83–99, 131–144 | the linear-cofactor back end of this package's free-scale forms, with radical weight 4 |

The weak front reads the scale as `Y = v·q` and does not force `q³·(2v + 1)` syntactically.
The saturated carrier `zc = T·Dcar + K·M + H·(v − q²)`, `M = 2q²`, `S = M⁵·H·r·s` restores
it: a zero forces `S ∣ Ac`, hence `M ∣ zc`, hence `v = (1 + 2v')·q²`.

`P135WValue.back` is the record of the back-end registers, over `P137Front.front`:

    Dguard = Budget − 4;   Pg = s·Dt;   P = Dt + Pg·(Dguard·Pg);
    B = A·(r·Dm);          U = c²·(r·Dm);
    strong = (Delta·c²)·(A·U);   Df = 1 + strong;   Q = Delta·strong;   δ = Q − 1;
    b = (c − R) + T·(4·(A·U));   V = Df·b − c;      Cy = V·(Q·V) − 1;
    pa = δ·Z²;   pb = P·(δ·S²);  pc = Cy·(Df·(B·(4·S²)));
    output = (pa + pb − pc)² − pb·(4·pa).

In closed form `B = A·r·Dm`, `Df = 1 + Δ·c⁴·B`, `Q = Δ²·c⁴·B`, `P = Dt·(1 + (Budget − 4)·Dt·s²)`,
and the output is the norm `𝓘² − 𝓣²·P` with `𝓘 = δ·Z² + δ·S²·P − 4·S²·B·Df·Cy` and
`𝓣 = 2·δ·Z·S` (`value_eq_product`). Against package 137's single product `δ·Z² − S²·BP·Df·Cy`,
the guard `P` is not multiplied into the cofactor; it is a second radical, and the factors `A`
and `Dm` sit inside the linear cofactor `B`, so there is no separate square condition on `r` or
`Dm`.

## Route

In every model `V` of `𝗜𝚺₁`, the equation has a zero in the ring of differences `DiffRing V`
iff machine 215 halts internally.

**Soundness** (`P135WFold.sound`).

* `P135WRoots`, congruences: `Budget ≡ 0 (mod 4)` on the weak front, hence `P ≡ 1 (mod 4)`;
  `Df ≡ 1 (mod 4)`; `Q` is even.
* Nonvanishing: `δ`, `Df`, `Cy` and `P` are nonzero everywhere. At a zero `S ≠ 0` (the output
  at `S = 0` is `(δ·Ac²)²` with `Ac ≠ 0`) and `Z ≠ 0` (otherwise `δ·P = 4·B·Df·Cy`, odd
  against even).
* Norm extraction (`norm`): `P = g²` and `δ·(Z − S·g) = 2·S·w` with `w² = B·Df·(δ·Cy)`.
* The three squares (`roots`): `B`, `Df` and `Da = δ·Cy` are pairwise coprime by ring Bézout
  identities, so each is a square with a positive root.
* The guard: `Dt` is coprime to its cofactor in `P`, so it is a square (`Dt_square`), and the
  positive cofactor with `s ≠ 0` gives `Budget > 0` (`budget_pos`).
* The descent: for `c ≠ 0` the adjacent equation `Q·V² − (Q − 1)·y² = 1` holds (`descent`);
  in both cases `S ∣ Ac` (`S_dvd_Ac`).
* `P137Bootstrap.recover` gives the scale `v = (1 + 2v')·q²` from `S ∣ Ac`, and the transfer
  lemmas of `P137Front` identify the weak registers at `Function.update x 5 v'` with package
  138's.
* `ZRows/StrongFold.strong_fold`, applied with `I₀ = c²·b₀` where `B = b₀²`, and `H ∣ Kq⁵`
  give `P138Rank.Folded` (`P135WFold.folded_of_zero`); `P138Leaf.halt_of_folded` gives the
  halt. The leaf chain of package 138 is reused unchanged.

**Completeness** (`P135WComplete.complete`).

* The canonical record of package 138 (`P138Canonical.canonical`) is read at the new scale
  `v = (1 + 2·v_old)·q²`; `P137Complete.weak_regs` identifies the weak registers with the
  canonical ones.
* `guard`: the discriminant `Budget − 4` is package 138's own, so the Pell pair of
  `P138Guard.guard` is reused and restated in the ring: `g² = 1 + (Budget − 4)·τ²·s²`, hence
  `P = (τ·g)²`.
* `interp`: the strong pair of the linear cofactor over the canonical record, without a point:
  `u`, `r`, `f` with `r·(a + 2)·d² = u²` and `1 + Δ·c⁴·u² = f²`, and for every residue target
  modulo `s·r` a value `T` and an ordinate `y` with `Q·V² − (Q − 1)·y² = 1`. The modulus
  `u·(s·r)` divides the fourth power of the interpolation ordinate only, so the quartic
  interpolation `ZRows/QuarticInterpolation.supported_interpolation4` is used.
* Carrier: as in `P137Complete`, a root of `(t² + 3)(t³ − 19)` modulo `s·r`
  (`ZRowsIntersective19.root`) gives `Ac = S·H⁴·e0`. The linear unknown
  `n = H⁴·e0 + 2·u·f·y + τ·g` makes `Z = S·(2·u·f·y + τ·g)`, and `value_eq_zero_of` closes the
  norm form.

No three-square theorem and no division is used.

## Modules

New modules:

| Module | Lines | Content |
|---|---|---|
| `P135W/P135WValue` | 179 | `Back`, `back`, `value`; register equations by `rfl`; closed forms; `value_eq_product`, `value_S_zero`, `value_eq_zero_of` |
| `P135W/P135WRoots` | 415 | congruences, nonvanishing, `norm`, `roots`, `Dt_square`, `budget_pos`, `descent`, `S_dvd_Ac` |
| `P135W/P135WFold` | 185 | `folded_of_zero`, `sound` |
| `P135W/P135WComplete` | 245 | `guard`, `interp`, `complete` |
| `P135W/P135WSyntax` | 489 | the literal, generated node for node from the JSON; `evalRing_literal`; `literal_zero_iff` |
| `P135W/IPRAInteger135W` | 90 | `expression`, `bridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` |

Reused unchanged: `P137/P137Front`, `P137/P137Bootstrap` and the transfer lemmas of
`P137/P137Complete` (the weak front and the saturated carrier); `ZRows/StrongFold` and
`ZRows/QuarticInterpolation`; the guard, the canonical record and the leaf chain of package 138.

The three endpoints say that the native, standard and equality-only iPRA theories each prove
`nativeNoZero (signedSplit expression)` equivalent to `∼mappedNativeRefutation embedding`,
the Foundation ZFC consistency predicate: the equation has no integer zero iff Con(ZFC). The
equality-only theory proves the order-erased form.

Every module was elaborated serially, one target per `lake` call, with no errors. The axiom
reports of `bridge` and of the three endpoints are `propext`, `Classical.choice` and
`Quot.sound`.

## Checkers

[`tools/gen_literal135w.py`](tools/gen_literal135w.py) generates `P135W/P135WSyntax.lean`. With
`--check` it confirms:

* the JSON's pinned SHA-256, variable list, node count, output node, operation counts, exact
  degree and `coefficient_binding`;
* that every named register of the JSON is mapped to exactly one field of `P137Front.front`
  (front and carrier) or of `P135WValue.back` (back end), or is the output; two nodes carry two
  names (`q2` and `qscale`; `Budget` and `base_budget`);
* that the regeneration is byte-identical and the Lean literal matches the JSON node for node;
* numeric agreement, modulo `2¹²⁷ − 1`, with an independent transcription of the closed form
  of `PROOF.md` §1 (weak-scale family, direct centre);
* the scale transfer: the value at `v = (1 + 2v')·q²` is the value of the cubic-scale
  transcription at `v'`, at 40 random points;
* that ten mutation controls are rejected (child, operation, literal, variable, coefficient,
  scale, linear slot, guard gate, operand order, output node).

Every named gate of the literal closes by `rfl`: the two record modules were written in the
JSON's operand order, so no gate needs `ring`.

[`tools/check_ports135w.py`](tools/check_ports135w.py) binds the six ports. The JSON's
coefficient leaves are symbolic, and the package does not ship its `scalar/coefficients/`
directory in this repository. The package's `MANIFEST_SHA256.json` pins the JSON, the binding
and the six payloads by byte count and SHA-256. The checker confirms the JSON's pin and
topology, resolves each coefficient pin to the repository copy that packages 131, 137, 138, 144
and 172 are bound to, and compares the payloads with `P138Ports.ports6` through the
transcription and drift guard of
[`check_ports138.py`](../p138-integer11/tools/check_ports138.py).

Both checkers are finite external evidence that the Lean literal is the published equation;
they are not Lean theorems.

## Remaining

Nothing for this form. The package's two other weak-scale variants (382 / 125 and 366 / 126)
are not covered here and are not Pareto points of the row: `PROOF.md` records them as
comparisons, dominated by the free-scale 352 / 125.
