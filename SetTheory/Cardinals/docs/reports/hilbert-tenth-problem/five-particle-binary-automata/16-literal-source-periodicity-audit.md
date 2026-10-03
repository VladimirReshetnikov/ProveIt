# Periodicity and positive-return audit

3 October 2026. This is an additional corollary audit. It leaves the original
macro audit, source tables, programs, and receipts unchanged.

## Conclusion

For every validated clean-loader input, the initial five-particle
configuration of the fixed binary reversible CA is periodic, equivalently
returns to itself at a positive time, **if and only if the simulated
Neary–Woods machine U halts**. On a halting input its least period is

    2Θ+2,

where Θ is the forward **CA microedge count**, computed by applying the
compiler's branch clock to every edge of the literal two-counter run.
It is not the number of TM steps, virtual instructions, five-counter steps,
or literal two-counter steps.

The positive-return/periodicity problem for exactly five particles under
this one fixed CA is recursively enumerable complete under computable
many-one reductions, using the stated finite-input universality dependency.
Conditional on the Report 12 Four-mass decision theorem, five is the sharp
mass threshold for undecidability of this particular decision problem in
the stated binary, one-dimensional, finite-zero-background,
number-conserving CA model.

## 1. Sources and audit scope

The upper-bound argument uses:

- The pinned literal `source.json`, SHA-256
  `38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a`
- The clean input family and finite source simulation proved in `PROOF.md`
  and `independent-macro-audit.md`
- The all-configuration source partial-injection check, including no
  incoming `START` and no outgoing `HALT`
- The copied `compiler-reference/COMPILER_PROOF.md`, especially Sections
  4–7 and 10, for the admissible micro-path, signed reflection dynamics,
  and full-shift binary reversible CA construction
- The published finite-input universality of the specified primary TM,
  as documented separately in this release

This audit checks the implication and the formerly missing nonblocking
premise. It is not a new independent proof of the compiler's all-input swap
lemma, the primary TM universality theorem, or the Report 12 lower bound.

## 2. Why the nonblocking premise holds for this loader

A clean source input has the form

    (START, C·2^L·3^R·5^T, 0),

with natural `L,R,T`, positive `C` coprime to 2310, and initial encoded
history/work counters both zero. The advertised tape loader uses `T=0,C=1`.
Its scanned input symbol is zero and both half tapes are finite.

Every non-halt instruction of the 528-instruction virtual program is an
`ADD` or a combined positive-decrement/zero-test `SUB`. Each is enabled on
every natural register vector. Its temporary loops terminate on their
simulation inputs by the proved decreasing ranks. Its sole designated
terminal is `HALT`, corresponding to the unique undefined primary TM cell.

Splitting `SUB` adds a decrement only after a positive test. Normalization
adds only finite identity chains. Each enabled history macro terminates
with clean work counter and correct data, and each enabled prime macro
terminates with physical scratch counter zero and the correct encoding.
All durations are finite positive integers. The initial clean values give
the base case for composing those invariants.

Consequently a clean-loader literal run has exactly two possibilities:

1. It reaches `HALT` after finitely many steps, exactly when U halts
2. It continues infinitely, exactly when U does not halt

It cannot stop at another control, get trapped in a disabled internal
test, or spend infinitely many steps simulating one enabled source step.
This assertion is deliberately restricted to clean-loader inputs.
Malformed encodings can still block elsewhere, and may therefore produce
finite reflected cycles unrelated to U's halting.

## 3. Exact reflected orbit and its least period

Write `x0,x1,...` for the unsigned admissible CA micro-path beginning at
the loaded home configuration. The literal `START` control has no incoming
branch at any counter values. Subdivision therefore leaves `x0` with no
predecessor. The unsigned micrograph is a partial injection.

No node on the forward micro-path can repeat. Indeed, if `xi=xj` for
`i<j`, then for `i>0`, uniqueness of predecessors gives
`x(i−1)=x(j−1)`. Repeating this inference gives `x0=x(j−i)`, with
`j−i>0`, so `x(j−i−1)` is a predecessor of `x0`, a contradiction. The
case `i=0` gives that contradiction immediately.

If U halts, let `xΘ` be its halt home after Θ microedges. The compiler's
one-step dynamics, edge matching followed by sign flip, has the orbit

    x0+, x1+, ..., xΘ+, xΘ−, x(Θ−1)−, ..., x0−, x0+.

The forward nodes are distinct by the preceding argument, and positive
and negative encodings are distinct by their assigned head gaps. Thus the
display contains exactly `2Θ+2` distinct states before the first return.
This proves the least period, not merely a period upper bound.

If U does not halt, Section 2 gives an infinite source path. Each compiled
edge has finite positive duration, so its CA micro-path is also infinite.
The CA remains on its positive copy and never reflects. Its nodes are
distinct, hence no positive return occurs.

For the base literal source, the compiler clock defining Θ is

    Θ = sum over literal executed branches e of τe,

where a zero-update branch has `τe=1`, and a nonzero-update branch using
pre-update selected counter `c` and delta `Δ` has

    τe = 3+2(Z+c)+Δ−4S.

Use the base-source constants `S=1019018` and `Z=20380380`. The Section 9
clean-target wrapper is a different enlarged source with different constants;
its `4Θ+6` full reflected period must not be substituted here.

## 4. Recursive-enumerability completeness

The CA is fixed, has finite radius, fixes the zero configuration, and has
an effective finite-rule description. Its astronomical size does not affect
computability. From any finite support one can compute the next finite
support and compare it exactly with the initial support. Forward simulation
therefore semidecides positive return. In particular the language of
positive-return inputs with exactly five occupied sites is recursively
enumerable.

The finite primary universal-machine program/data encoding, followed by
the explicit tape loader and five-particle encoding, is a computable map
to exactly-five-particle configurations of this one fixed CA. Sections 2–3
make membership equivalent to primary-machine halting. The stated
universality dependency therefore gives a computable many-one reduction
from the halting problem, proving r.e.-hardness. Together with membership,
this gives r.e.-completeness.

This is a fixed-CA statement with variable finite configurations, not a
construction that changes the CA rule for each simulated program.

## 5. Conditional lower bound from Report 12

The dependency is the companion report *Four mass units and exact
reachability*, Theorem 1.1, “Four-mass decision theorem,” in
`companion-report12/four-mass-decidability.tex` of the five-particle release.
Its theorem statement was read and the TeX hash independently checked:

    803bf0c4194bb9d0f1942e6ad3eb762c79d7a811bd785742ee63f0c46a775595.

The parent supplied the associated PDF hash:

    0d1280e962e64e8e13486aaac0fae2498ac908f37feeeffba0d682df865f3f5e.

The dependency assumes a fixed one-dimensional deterministic,
time-independent, translation-equivariant, finite-radius, finite-alphabet
CA with a fixed unique zero-weight vacuum, positive integer weights for
non-vacuum symbols, finite-support mass conservation, and at most one
weight-one symbol. It asserts decidability of specified finite-configuration
reachability at mass at most four, with procedures effective from the rule,
radius, and weights. The binary model with weights 0 and 1 satisfies those
hypotheses; reversibility is an additional restriction and causes no problem.

For every finite configuration `x`,

    there exists t>0 with F^t(x)=x
    if and only if
    x is reachable from F(x) at some time s≥0.

The equivalence is the substitution `t=s+1`. Computing `F(x)` preserves
mass. Thus the Report 12 exact-reachability decision procedure, applied to
initial configuration `F(x)` and specified target `x`, decides positive
return whenever the initial mass is at most four. It also correctly
recognizes fixed points because zero-time reachability is permitted.

Conditional on the correctness of that dependency, no CA in this model has
an undecidable positive-return problem on configurations of mass at most
four. The fixed reversible binary CA above has an r.e.-complete
positive-return problem at exactly five particles. Therefore the threshold
five is sharp **for periodicity/positive return in this model**. This does
not independently establish the lower-bound theorem, a priority claim, or
a threshold for every possible definition of computational universality.

## 6. Separate arithmetic check of the class-expansion ledger

This check is included only to record the additional requested source
counts; it is independent of the periodicity proof. `source.json` has
`J=0`, so each counter's domain class is either zero or positive. Expanding
each branch over its enabled product classes gives:

| Update / guard | Literal rows | Allowed product-class cells | Positive-class coordinate occurrences |
|---|---:|---:|---:|
| decrement / positive | 32630 | 65260 | 97890 |
| zero update / zero | 23429 | 46858 | 23429 |
| zero update / positive | 52036 | 104072 | 156108 |
| zero update / true | 30 | 120 | 120 |
| increment / true | 33436 | 133744 | 133744 |
| **Total** | **141561** | **350054** | **411291** |

Thus the directly verified source quantities are

    B = 350054,
    r = 411291,
    P = 65260+133744 = 199004

where `P` counts nonzero-update normalized cells, not literal moving rows.
In particular, `B+r=761345` and `2B=700108`.

If the separate residual core contributes exactly two additional variables
and four additional squared residuals per time slice, plus one final
square, then its proposed totals are arithmetically

    (B+r+2)H = 761347H variables,
    (2B+4)H+1 = 700112H+1 squares.

Only the source counts and this arithmetic have been checked here. The
residual definitions supplying the extra two variables, four squares, and
final square were not supplied to this audit; no verification of them or
their semantic sufficiency is asserted.
