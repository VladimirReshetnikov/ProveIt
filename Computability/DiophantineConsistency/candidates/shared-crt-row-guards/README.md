# Integer quartic with row-derived nonnegativity

The entire fixed polynomial is `expanded_polynomial.json`. Equivalently it
is the sum of the squares of every quadratic residual in `equation.json`.
All **6,604 coordinates range over unrestricted integers**.

| Variables | Quadratic rows | Exact degree | Quartic monomials | Coefficient height |
|---:|---:|---:|---:|---:|
| **6,604** | **3,815** | **4** | **31,201** | **127,299,660** |

The frozen parent is the complete 3,328-natural-variable
`shared-crt-power-slack-reduction/affine` equation. Guarding all its 1,395
semantic inputs separately would use 7,513 integer variables. Here only
1,092 inputs receive guards. A finite ordered certificate then proves all
3,328 original coordinates nonnegative directly from the actual integer
row equations, removing 303 guards and 909 auxiliary coordinates.

The certificate uses one elementary rule:

> If an actual zero row gives `c*x=P`, where `c` is a positive integer
> and every coefficient of `P` is nonnegative, then `x>=0` whenever the
> variables with odd powers in `P` are already known nonnegative.
> Even powers are nonnegative for all integer values.

`NONNEGATIVITY.json` supplies the 1,092 seeds and all 2,236 ordered
derivation steps. The checker reconstructs each rule from its indicated
original row; it trusts no recorded polynomial rewrite or natural-compiler
semantics. Of the steps, 2,220 have `c=1` and sixteen have `c=4`.
There are 917 occurrences of monomials needing no sign premise because
all their exponents are even.

This first candidate uses no inverse-product sign inference, capped
positive lower bounds, power theorem, or Pell classification to eliminate
guards. The selection is deterministic greedy deletion among the original
semantic guards; no minimum guard-count claim is made.

## Proof over arbitrary integer zeros

For every seed `x`, add three fresh unrestricted integers `a,b,c` and
the quadratic residual

```
x-a^2-b^2-c(c+1).
```

Every such zero row forces `x>=0`, since `c(c+1)>=0` for every integer
`c`. At a zero of the complete sum of squares, every original and added
residual vanishes. Induct through the ordered certificate. At one step,
multiply its indicated row by the sign of the output coefficient. The
result is `|c|*x=P` with positive output coefficient and the exact
nonnegative-coefficient right side checked from the row. Previously
certified variables account for every odd exponent. The other powers
are even, hence nonnegative independently of their signs. Thus `P>=0`
and `x>=0`. After 2,236 steps every original coordinate is natural.

This argument is about arbitrary integer solutions of explicit quadratic
equations. It does **not** assume that a natural compiler is correct, that
a Pell or power graph has its intended interpretation, or that an
original semantic input is nonnegative because of its name or kind.
Natural-parent semantics is used only after all its coordinates have
been proved nonnegative.

Conversely, every natural parent zero extends to an integer zero of the
new equation. Each natural seed has a representation
`x=a^2+b^2+c(c+1)`: apply Legendre's three-square theorem to `4x+1`,
which is positive, congruent to one or five modulo eight, and not
divisible by four. Exactly one representing square is odd and two are
even. Write them as `(2c+1)^2,(2a)^2,(2b)^2`, subtract one, and divide
by four. Choose fresh witnesses independently for each seed. All original
rows are preserved verbatim, and all added guards then vanish.

Consequently the new integer equation has a zero exactly when the frozen
natural parent does. This is a complete unbounded ordinary mathematical
equivalence. Composing it with the parent's explicitly named C222-to-ZF
and constructible-choice calibration gives the same ordinary
ZFC-formalizable refutation equivalence. No consistency or unsolvability
assertion is assumed. Lean remains paused; a new encoded internal-ZFC
derivation is not supplied here.

## Concrete row examples and counts

The endpoint gives `y=M0+r0+2`, so its semantic `y` guard is redundant.
Other steps certify power-certificate coordinates `Y,T,B,V` from the
literal surrounding equations. For sixteen constant-base power calls,
the actual row `4*A-T-5=0` gives `4*A=T+5>=0`; it licenses `A>=0`
without an `A` guard despite its nonmonic coefficient. These claims are
checked from the full indexed rows, rather than inferred from macro
labels.

The exact dimension and row counts are

```
variables = 3328+3*1092 = 6604,
rows      = 2723+1092   = 3815.
```

Appending quadratic guards preserves degree at most four. The last
fresh auxiliary occurs in one guard only, and its fourth-power
coefficient is exactly one in the single collected polynomial, proving
degree exactly four. Full expansion verifies every one of the 31,201
nonzero monomials and the actual coefficient height. The initial
8,619-integer guarded prime-lift candidate and all frozen natural parents
remain unchanged. Comparisons are local construction comparisons, not
global minimality claims.

## Files, pins and replay

`PARENT_PINS.json` binds both complete frozen natural files.
`equation.json` retains their full variable/row prefix and appends only
the fresh guards. `NONNEGATIVITY.json` is the independently checked
certificate. The numerical polynomial contains no parameters, variable
exponents, binomial/factorial operators, hidden native payloads, or
unexpanded bounded quantifiers.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_shared_crt_row_guards.py --check
python3 -B -O Computability/DiophantineConsistency/tools/build_shared_crt_row_guards.py --check
python3 -B Computability/DiophantineConsistency/candidates/shared-crt-row-guards/check.py
python3 -B -O Computability/DiophantineConsistency/candidates/shared-crt-row-guards/check.py
```

The checker imports no builder or closure search. It verifies the exact
original prefix, every ordered integer inference, guard coverage,
freshness, all quadratic indices, full collected expansion, liveness,
and the degree-four coefficient. Normal and optimized Python runs pass.
The small three-square controls supplement Legendre's theorem and are
not offered as its proof. The original archive and frozen candidates
are not modified by generation or verification.
