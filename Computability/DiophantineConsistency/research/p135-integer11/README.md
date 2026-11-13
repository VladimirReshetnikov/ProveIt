# Packages 135 and 144: five eleven-integer equations (352/125 to 308/140): iPRA endpoints (closed)

This record documents the iPRA endpoints of five equations in eleven unknowns over ℤ:

| Degree / operations | JSON | Package |
|---|---|---|
| 352 / 125 | [`free_cofactor11_none.json`](../../con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/free_cofactor11_none.json) | 135 |
| 340 / 129 | [`free_cofactor11_simple.json`](../../con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/free_cofactor11_simple.json) | 135 |
| 328 / 130 | [`free_cofactor11_sharp.json`](../../con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/free_cofactor11_sharp.json) | 135 |
| 316 / 133 | [`free_whole_center11_c316.json`](../../con-zfc-diophantine-forms/144-shared-certificates-round18/scalar/free_whole_center11_c316.json) | 144 |
| 308 / 140 | [`free_whole_center11_c308.json`](../../con-zfc-diophantine-forms/144-shared-certificates-round18/scalar/free_whole_center11_c308.json) | 144 |

The packages' own proofs are
[135's `PROOF.md`](../../con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/PROOF.md)
and
[144's `PROOF.md`](../../con-zfc-diophantine-forms/144-shared-certificates-round18/scalar/PROOF.md).
The Lean proof does not follow them separately: all five equations are instances of the
linear-cofactor circuit of [package 172](../p172-integer11/README.md), and the theorems of
`Lean/DiophantineConsistency/LinCof/` were stated for that whole family. The modules added here
are a value module, five generated syntax modules, one small joining lemma and two endpoint
modules.

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`, each integer unknown written as a difference of two naturals.
The unknowns `j C z h r v w T c n s` and the six ports `beta K0 MC MF cone_A cone_B`
(`P138Ports.ports6`, the source34 tuple) are those of
[package 138](../p138-integer11/README.md).

## One circuit, five centres

Each equation is `LCValue.valueK p x κ ω Λ ψ wt` at the 300-type slots
`κ = k300`, `ω = kq300`, `Λ = L300` (so `SlotLaw` holds with `e = 1`). The five differ only in
the centre `ψ` and the radical weight `wt` of `pc = wt·S²·B·Df·Cy`:

| Form | Centre `ψ` (`P135Value`) | Weight |
|---|---|---|
| 352 / 125 | none: `0` | `4 = 2²` |
| 340 / 129 | `psi340 = 2·A²·U·V` | `4` |
| 328 / 130 | `psi328 = (2Δ + 1)·U·V` | `4` |
| 316 / 133 | `psi316 = ((8Δ + 4)·U − r·c⁴)·V` | `64 = 8²` |
| 308 / 140 | `psi308 = psi316 + 2·U³·T·(c² − 2)` | `64` |
| 300 / 144 (package 172) | `psi300` | `1024 = 32²` |

A larger centre lowers the degree and costs operations; that trade is the whole of this stretch
of the eleven-integer Pareto row. Each centre reads registers of the circuit at zero slots,
none of which depends on the unknown `n = x 9`, so `ψ (update x 9 t) = ψ x` holds by `rfl`.

In the JSON DAGs, nodes 0 to 132 are identical in all five equations.

## Route

`LinCof/LCFamily.zero_iff_halts` joins the two generic theorems of package 172:

* **Soundness** is `LCLeaf.sound`, which uses the weight only through `LCNorm.Weight wt`
  (`wt` is a nonzero even square: `weight4`, `weight64`) and does not read the centre: at a
  zero the centre is absorbed into the unknown `n`.
* **Completeness** is `LCComplete.lc_complete300`, which takes the weight as `wt = lw²` for an
  arbitrary ring element `lw` (`2`, `8`) and uses the centre only through its independence of
  `x 9`.

The statement is: for every such centre and weight, the circuit has a zero in `DiffRing V`, for
`V` a model of `𝗜𝚺₁`, iff machine 215 halts internally. Each of the five bridges
`IntegerModelBridge expression` is this lemma composed with the generated `literal_zero_iff`.
No new arithmetic was needed for these five points.

## Modules

| Module | Content |
|---|---|
| `P135/P135Value` | the centres `psi340`, `psi328`, `psi316`, `psi308`; `regs352`/`value352`, …, `regs308`/`value308` |
| `LinCof/LCFamily` | `zero_iff_halts` |
| `P135/P135Syntax352`, `P135Syntax340`, `P135Syntax328` | the three package-135 literals, generated node for node from the JSON; `evalRing_literal` (to `value352`, …); `literal_zero_iff` |
| `P144/P144Syntax316`, `P144Syntax308` | the same for the two package-144 literals |
| `P135/IPRAInteger135` | namespaces `Form352`, `Form340`, `Form328`, each with `expression`, `bridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` |
| `P144/IPRAInteger144` | namespaces `Form316`, `Form308`, the same |

The three endpoints say that the native, standard and equality-only iPRA theories each prove
`nativeNoZero (signedSplit expression)` equivalent to `∼mappedNativeRefutation embedding`,
the Foundation ZFC consistency predicate: the equation has no integer zero iff Con(ZFC). The
equality-only theory proves the order-erased form. This holds for each of the five equations.

Every module was elaborated serially, one target per `lake` call, with no errors. Axioms are
within `propext`, `Classical.choice` and `Quot.sound`.

## Checkers

[`tools/gen_literal135.py`](tools/gen_literal135.py) generates the five syntax modules
(`--form 352|340|328|316|308`). It reuses the parser, evaluator and comparison of
[`gen_literal172.py`](../p172-integer11/tools/gen_literal172.py). With `--check` it confirms,
for each form, the JSON's pinned SHA-256 and operation counts, that the regeneration is
byte-identical, that the Lean literal matches the JSON node for node, numeric agreement with
the closed form of the package's `PROOF.md` at a random point, that the literal is not one of
the other four, and that mutation controls are rejected (nine for 352, ten for the others).

The JSON writes three products in the opposite operand order to `LCValue.regsK`: the budget
product `(q2 − Derr)·(Yk·Yk)`, the weight gate `4·S²` of the three package-135 forms, and
`n·S` of 352 (which has no centre, so `Z = S·n − Ac`). The generator asserts exactly these
exceptions and closes them by `mul_comm` (the last by `ring`); the literal keeps the JSON's
order.

[`tools/check_ports135.py`](tools/check_ports135.py) binds the six ports. Neither package
ships its `coefficients/` directory in this repository; each package's `MANIFEST_SHA256.json`
pins the binding and the six payloads by byte count and SHA-256. The checker resolves each pin
to the repository copy that packages 138 and 172 are bound to, confirms that the two packages
pin the same seven files, and compares the payloads with `P138Ports.ports6`.

Both checkers are finite external evidence that the Lean literal is the published equation;
they are not Lean theorems.

## Remaining

Nothing for these five forms. Package 135's `weak_cofactor11_*.json` equations (the 398/121
point of the row) are not covered here.
