# Cofinal horizons and a deterministic beta modulus

## Scope and exact source

This ordinary proof strengthens the complete signed derived-label
factorial-carrier source from the incoming Round 14 packet, pinned in
ProveIt commit `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`.
Its files are:

- `report/direct_arithmetic.tex`, especially the complete factorial-weight
  Horn-flow equivalence and its constructive completeness;
- `report/direct_signed.tex`, final subsection (the separate 517-variable
  tradeoff);
- `direct/derived16_signed_shell/mixed_source.json` and `guarded.json`.

The source coordinate names used below are literal mixed-source names:

| Index | Name | Meaning |
|---:|---|---|
| 0 | `t0` | horizon offset, so `t=t0+16` |
| 1 | `x` | beta-encoded path |
| 2 | `y` | common beta-modulus parameter |
| 3 | `fact0.output` | proposed factorial `F` |
| 7 | `pow0.output` | proposed power `V` |
| 12 | `endpoint.r0` | slack in `y=F+1+r0` |

Raw-source and mixed-source coordinate indices are not interchangeable.
The new restrictions will be imposed on these names before any new
projection. Exact final counts are to be measured from the emitted
equations, not inferred from this argument.

## 1. The strengthening

Keep every parent arithmetic row. Make the following changes to its
nonnegative guards:

1. Replace `t0>=0` by `t0=s^2`, for one unrestricted integer `s`.
2. Replace the guard `F>=0` by `F>=1`, using the same ternary representation
   on `F-1`.
3. Delete only the guard `r0>=0`, and add the quadratic equation

   `y - V^2 - 3F + 1 = 0`.

Thus the deterministic choice is

`t=16+s^2`,    `y=V^2+3F-1`.

The parent ternary guard is exactly

`z=a^2+b^2+c(c+1)`.

It represents precisely `z>=0` over the integers. For the strengthened
factorial guard, the literal new row is therefore

`F-1-a^2-b^2-c(c+1)=0`.

No variable exponent occurs in either added row. The notation
`V=(Ft^2+1)^t` will be used only after the parent power representation has
been interpreted, or when constructing canonical witnesses.

## 2. Immediate soundness: all parent guards are restored

Take an arbitrary integer zero of the strengthened system. The new square
row gives `t0>=0`. The strengthened ternary row gives `F>=1`.
The unchanged endpoint row and the new deterministic row imply

`r0 = y-F-1 = V^2+2F-2 >= 0`.

This implication holds for every signed integer `V`; it does not assume
power semantics, factorial semantics, Pell classification, or a bound on
the proof. In particular `y>=2`, so every old presemantic lower bound on
`y` still holds.

Consequently all parent arithmetic rows and all parent domain predicates
hold. Fresh ternary witnesses can be supplied for the old `t0`, `F`, and
`r0` guards. The exact retained signed-source theorem applies without any
change in its ordering of sign, power, factorial, range, or CRT arguments.
It yields an actual finite C222 refutation, then the existing
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` calibration yields
ZFC refutability.

This is a strengthening of the source. It is not an assertion that every
old witness extends pointwise to a new witness.

## 3. Cofinal square horizons

Conversely, suppose a finite C222 refutation exists. Expand its proof DAG
to a finite tree, as in the parent construction. There are finitely many
rule occurrences, local parameters, and full constructor label sums
`J(a,b,c,d)`. Include the fixed truth-padding tuple's label sum too.
Let `H` be the maximum of 16, the number of tree steps, all those
parameters, and all those sums.

Choose any integer `s>=H`; then `t=16+s^2>=H`. This proves the required
cofinality without a square-root operation, a choice principle, or an
assumption that a refutation exists unconditionally. All the original
horizon inequalities hold, including those for branches not selected by
the proof. Insert truth steps until there are exactly `t` rows.

Set `F=t!` and `b=Ft^2+1`. Since `t>=16`, `F>=1`. Set `V=b^t`.
These canonical values obey the existing factorial and power requests.

## 4. A bound for every pending-product accumulator

The backward proof-tree expansion starts with a pending multiset of one
formula, falsity. Each step removes one pending conclusion and inserts
at most two premises; therefore a step increases the pending cardinality
by at most one. At every point during at most `t` steps, its cardinality
is at most `t+1`. Repeated formulas count with their multiplicities.
Truth labels have weight one and can simply be retained in this bound.

Every relevant label `j` lies between zero and `t`, because the horizon
dominates the full label sum for each selected local tuple. The parent's
weight is `W_j=1+jF`, including `W_0=1`. Since `t>=1`,

`1 <= W_j <= 1+tF <= 1+t^2 F = b`.

Hence every before- or after-step accumulator obeys

`1 <= S,S' <= b^(t+1) <= b^(2t) = V^2`.

The weak final inequality includes `t=1`; the actual source uses
`t>=16`. Truth padding leaves the accumulator unchanged, so it obeys the
same estimate. No bound is asserted on the external numerical code of
the whole proof; only this finite expansion is used.

## 5. The deterministic modulus meets every completeness obligation

Define

`y=V^2+3F-1`.

The base `b=Ft^2+1` is congruent to one modulo `F`, so
`V=b^t` and `V^2` are also congruent to one modulo `F`. It follows that
`F` divides `y`.

Also `F>=1`, so

`y>V^2>=S,S'` and `y>=F+1`.

These are exactly the beta-modulus conditions used by the parent's
constructive completeness: a positive multiple of `t!`, at least every
accumulator and at least `F+1`. The newly selected `y` is determined by
`t` and `F` before `x` is chosen; it does not depend on a CRT encoding,
the large common radix, or any Pell witness.

For completeness of the beta encoding, set
`m_i=1+(i+1)y`, `0<=i<=t`. If a prime divided `m_i` and `m_j` for
`i!=j`, it would divide `(i-j)y` but not `y`, hence would divide
`i-j`. Its size would be at most `t`, so it would divide `t!` and thus
`y`, a contradiction. The moduli are pairwise coprime. CRT gives a
nonnegative `x` with the prescribed accumulator residue at each step.
Each residue lies in `[0,y]`, strictly below its modulus. The Euclidean
quotients are therefore natural and at most `x`. Set
`r0=y-F-1`; it is nonnegative and satisfies the old endpoint row.

Now complete the original construction in its original order: calculate
`R`, `K`, the reciprocal-binomial modulus and its amplified power; choose
the nine independent representatives by the strengthened CRT; construct
the common digit radix; supply the exact/fused digit witnesses; and then
rebuild the square frame and the shared Pell witnesses for these new
data. All the original finite majorants were proved for arbitrary
admissible `x,y` and therefore apply to this particular choice.

The new `s` is the previously chosen integer. Supply a ternary guard for
`F-1` and keep every other required ternary witness. All new rows now hold.
Thus every finite refutation gives a full zero of the strengthened system.

## 6. Calibration and scope

The two directions establish zero-existence equivalence with the exact
parent signed source. They use elementary finite induction, factorial
divisibility, the finite CRT, the retained natural-number guard theorem,
and the parent's uniform arithmetic/calculus arguments. These arguments
are formalizable in ZFC without assuming its consistency. Composition
gives the same ZFC-provable equivalence between polynomial unsolvability
and syntactic `Con(ZFC)`.

The new restrictions are complete only because this source admits truth
padding and because its compulsory factorial power provides the stated
accumulator majorant. They are not generic substitutions for an arbitrary
nonnegative witness. In particular, forcing an arbitrary encoded residue
or a factorial itself to be a square would not be justified.

This note proves the new unbounded source step. The exact projection,
integral translation, final variable count, term count, coefficient height,
and quartic degree require their separate literal artifacts and checks.
No new Lean/Rocq proof or internal object-language derivation is claimed.

## 7. General reusable lemma

Suppose a proof-to-arithmetic construction permits all sufficiently large
integer horizons, has no more than two premises per rule, uses weights
`1+jF` with labels at most the horizon `t`, and already represents
`F=t!` and `V=(Ft^2+1)^t`. Suppose its beta modulus may be any positive
multiple of `F` exceeding all pending products. Then:

- the horizon can be restricted to `c+s^2` for any fixed admissible lower
  bound `c`;
- the beta modulus can be fixed to `V^2+3F-1`, provided `F>=1`;
- these restrictions preserve existence of certificates, while all new
  arithmetic equations remain quadratic in the retained coordinates.

The source-specific instance above discharges every hypothesis and uses
the fixed lower bound `c=16`.

## 8. A two-parameter family and an explicit failed generalization

More generally, for fixed integers `d>=1`, `kappa>=1` with
`(kappa-1)d>=2`, replace the factorial guard by `F>=d` and set

`y=V^2+kappa*F-1`.

Then `r0=V^2+(kappa-1)F-2>=0` before any semantics. In the canonical
construction one additionally requires the cofinal horizon to make
`t!>=d`; this is another finite lower bound on the horizon. Since
`V=1 mod F`, the divisibility `F|y` remains exact. The selected literal
equation uses `(kappa,d)=(3,1)`. The also-valid pair `(2,2)` is a separate
coefficient-height option and is not silently substituted into its
coefficient table.

Cofinality by itself does not justify replacing an arbitrary witness by
a square. For example, the positive integral solutions of

`x=3u+2`, `u>=0`

are unbounded, but none has `x=s^2`, since a square is zero or one modulo
three. The horizon argument succeeds because *every* sufficiently large
horizon is admissible after truth padding. It would be invalid for an
arbitrary encoded CRT residue, or for the comparison-base quotient of a
Pell certificate. The beta-modulus restriction uses its own explicit
congruence `V=1 mod F`; it is not licensed merely by large size.
