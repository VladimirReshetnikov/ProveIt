# Package 137: the eleven-integer weak product equation 648/115: iPRA endpoints (closed)

This record documents the iPRA endpoints of one equation in eleven unknowns over ℤ: package
137's weak product form
[`weak_product11_none.json`](../../con-zfc-diophantine-forms/137-odd-helpers-saturated-carriers/integer/weak_product11_none.json),
of exact degree 648 with 115 operations (73 `mul`, 23 `add`, 19 `sub`). On the eleven-integer
Pareto row it lies between package 131's 810 / 112 and package 125's 488 / 118. The package's
own proof is
[`PROOF.md`](../../con-zfc-diophantine-forms/137-odd-helpers-saturated-carriers/integer/PROOF.md).

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`, each integer unknown written as a difference of two naturals.
The unknowns `j C z h r v w T c n s` and the six ports `beta K0 MC MF cone_A cone_B`
(`P138Ports.ports6`, the source34 tuple) are those of
[package 138](../p138-integer11/README.md).

## The circuit

Against package 138:

| | Package 138 | Package 137 weak product |
|---|---|---|
| scale register | `Y = q³·(2v + 1)` | `Y = v·q` (the *weak front*) |
| carrier | `zc = K + T·H`, modulus `H` | `zc = T·Dcar + K·M + H·(v − q²)`, `M = 2q²`, modulus `Dcar = H·M` (the *saturated carrier*) |
| linear slot | `Z = n·S − Ac`, `S = H·r·s` | `Z = n·S − Ac`, `S = M⁵·H·r·s` |
| guard discriminant | `D4 = Budget − 4` | `D4 = 4·(3·Budget − 4)` |
| output | one outer square condition | the same shape: `δ·Z² − S²·BP·Df·Cy` |

The weak front does not force the scale `q³·(2v + 1)` syntactically. The carrier restores it:
a zero forces `S ∣ Ac`, hence `M ∣ zc`, hence `M ∣ H·(v − q²)`, and `H` is coprime to `M`, so
`v = (1 + 2v')·q²` and `Y = q³·(2v' + 1)`. Every register that does not read `v` is the same
term as in `P138Value.regsK`.

`P137Front.front` is the record of the front and carrier registers and `P137Value.back` that of
the back end:

    P = Dt + Pg·(D4·Pg),  Pg = s·Dt;      BP = P·Dm;        U = A·(r·c²);
    strong = (BP·U)·(Delta·U);            Df = 1 + strong;  Q = Delta·strong;
    b = (c − R) + T·(4·BP·U);             V = Df·b − c;     Cy = V·(Q·V) − 1;
    output = Z·(δ·Z) − Cy·(Df·(BP·S²)),   δ = Q − 1.

The front and the carrier are shared, node for node, with package 135's
`scalar/weak_cofactor11_none.json` (398 / 121), which is why they have a module of their own.

## Route

In every model `V` of `𝗜𝚺₁`, the equation has a zero in the ring of differences `DiffRing V`
iff machine 215 halts internally.

**Soundness** (`P137Fold.sound`).

* `P137Roots`: at a zero, `δ`, `Df`, `Cy`, `P`, `BP` and `S` are nonzero (the output at
  `S = 0` is `δ·Ac²` with `Ac ≠ 0`). `BP`, `Df` and `Da = δ·Cy` are pairwise coprime by ring
  Bézout identities, and `δ·Z = S·w` with `w² = BP·Df·Da`, so each of the three is a square
  with a positive root: `Df ≡ 1 (mod 4)` excludes a negative square, and `BP < 0` would force
  `Df < 0`. Then `P > 0` and `Budget > 0`, the adjacent descent `Q·V² − (Q − 1)·y² = 1` holds
  for `c ≠ 0`, and `S ∣ Ac`.
* `P137Bootstrap.recover`: from `S ∣ Ac`, the scale `v = (1 + 2v')·q²`. The step from
  `M⁵ ∣ Ac` to `M ∣ zc` is `ZRows/ReducedFraction.dvd_of_pow5`, a reduced-fraction argument
  for the monic quintic `Ac`.
* `P137Front`, transfer lemmas: at `Function.update x 5 v'` and the native index, the weak
  registers are package 138's.
* `ZRows/StrongFold.strong_fold`, applied with `I0 = |A|·|r|·c²·p0`, and `H ∣ Kq⁵` give
  `P138Rank.Folded` (`P137Fold.folded_of_zero`); `P138Leaf.halt_of_folded` gives the halt. The
  leaf chain of package 138 is reused unchanged.

**Completeness** (`P137Complete.complete`).

* The canonical record of package 138 (`P138Canonical.canonical`) is read at the new scale
  `v = (1 + 2·v_old)·q²`; `weak_regs` identifies the weak registers with the canonical ones.
* `guard`: `Budget > 64`, and `3·Budget − 4 = 3·(Budget − 2) + 2` is not a square because no
  square is 2 modulo 3 (`not_square_mod_three`). So `4·(3·Budget − 4)·τ²` is not a square and
  the Pell existence theorem gives `g² = 1 + 4·(3·Budget − 4)·τ²·s²`; then `P = (τ·g)²` and
  `BP = (d·τ·g)²`.
* `interp`: the supported-modulus interpolation of package 138, restated over the canonical
  record without a point and without package 138's guard hypothesis.
* Carrier: `K = H·κ` and `v − q² = M·v_old` give `zc = M·H·(T + κ + v_old)`; a root of
  `(t² + 3)(t³ − 19)` modulo `s·r` (`ZRowsIntersective19.root`) gives `Ac = S·H⁴·e0`; the
  linear unknown `n = H⁴·e0 + p0·f·y` makes `Z = S·p0·f·y`, and `value_eq_product` closes the
  zero.

No three-square theorem and no division is used.

## Modules

| Module | Lines | Content |
|---|---|---|
| `ZRows/ReducedFraction` | 80 | `reduced_fraction`, `dvd_of_pow5`, `dvd_of_dvd_mul_coprime` |
| `P137/P137Front` | 303 | `Front`, `front`; register equations by `rfl`; closed forms; the transfer to `P138Value.regsK` |
| `P137/P137Value` | 150 | `Back`, `back`, `value`; `value_eq_product`, `value_S_zero` |
| `P137/P137Bootstrap` | 209 | congruences and coprimality of the weak front; `M_dvd_zc`, `recover`, `H_dvd_Kq5` |
| `P137/P137Roots` | 360 | nonvanishing, the three squares, positivity, `descent`, `S_dvd_Ac` |
| `P137/P137Fold` | 221 | `folded_of_zero`, `sound` |
| `P137/P137Complete` | 338 | `guard`, `interp`, `weak_regs`, `complete` |
| `P137/P137Syntax` | 473 | the literal, generated node for node from the JSON; `evalRing_literal`; `literal_zero_iff` |
| `P137/IPRAInteger137` | 85 | `expression`, `bridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` |

The three endpoints say that the native, standard and equality-only iPRA theories each prove
`nativeNoZero (signedSplit expression)` equivalent to `∼mappedNativeRefutation embedding`,
the Foundation ZFC consistency predicate: the equation has no integer zero iff Con(ZFC). The
equality-only theory proves the order-erased form.

Every module was elaborated serially, one target per `lake` call, with no errors. The axiom
reports of `bridge` and of the three endpoints are `propext`, `Classical.choice` and
`Quot.sound`.

## Checkers

[`tools/gen_literal137.py`](tools/gen_literal137.py) generates `P137/P137Syntax.lean`. With
`--check` it confirms:

* the JSON's pinned SHA-256, variable list, node count, output node, operation counts, exact
  degree and `coefficient_binding`;
* that every named register of the JSON is mapped to exactly one field of `P137Front.front`
  (front and carrier) or of `P137Value.back` (back end), or is the output; one node carries
  two names (`q2` and `qscale`);
* that the regeneration is byte-identical and the Lean literal matches the JSON node for node;
* numeric agreement, modulo `2¹²⁷ − 1`, with an independent transcription of the closed form
  of `PROOF.md` §1;
* the scale transfer: the value at `v = (1 + 2v')·q²` is the value of the cubic-scale
  transcription at `v'`, at 40 random points;
* that ten mutation controls are rejected (child, operation, literal, variable, coefficient,
  scale, linear slot, guard constant, operand order, output node).

Every named gate of the literal closes by `rfl`: the two record modules were written in the
JSON's operand order, so no gate needs `ring`.

[`tools/check_ports137.py`](tools/check_ports137.py) binds the six ports. The JSON's
coefficient leaves are symbolic, and the package does not ship its `integer/coefficients/`
directory in this repository. Three pin sets of the package (the release `MANIFEST.json`,
`integer/MANIFEST.json` and `integer/SOURCE_PINS.json`) pin the binding and the six payloads
by byte count and SHA-256. The checker confirms that they agree, resolves each pin to the
repository copy that packages 131, 135, 138, 144 and 172 are bound to, compares the payloads
with the package's `integer/CHECK.json` (status, coefficient flags, the recorded topology of
this equation and the recipe `beta = 2^d − 1`), and compares them with `P138Ports.ports6`
through the transcription and drift guard of
[`check_ports138.py`](../p138-integer11/tools/check_ports138.py).

Both checkers are finite external evidence that the Lean literal is the published equation;
they are not Lean theorems.

## Remaining

Nothing for this form. The package's three other eleven-integer equations are not covered
here and are not Pareto points of the row; `PROOF.md` itself records them as audited
comparison constructions:

* `weak_product11_simple.json` (640 / 118) has a higher degree than package 125's 488 / 118
  at the same operation count;
* `free_product11_none.json` (580 / 119) has a higher degree than package 125's 464 / 119 at
  the same operation count;
* `free_product11_simple.json` (574 / 122) has both a higher degree and more operations than
  package 125's 464 / 119.
