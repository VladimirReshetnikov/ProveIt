# Internal negative norms: author receipt

27 October 2026. The final 176-line main, 38-line Checks and executed
driver were fully self-read before compilation. The final private pair
passes in 8.755/1.957 seconds, with an empty main log and seven axiom
reports containing only `propext`, `Classical.choice`, `Quot.sound`.
The sources and evidence are frozen for independent ROOT review.

Every theorem ranges over an arbitrary internal IΣ1 arithmetic model.
`square_mod_four` derives the actual remainder alternatives from internal
even/odd decomposition. `square_discriminant_ne_negative` then proves
`x*x+t*t+1 != A*A*t*t` uniformly, including `A=0`, `A=1` and `t=0`.
The main discriminant identity `(a+1)*(a+3)+1=(a+2)^2` gives the main
and strong-factor exclusions. The square-coefficient auxiliary client
uses `A=S`, `x=S*v` and needs no preceding strong-norm equation.

`consecutive_negative_descent` takes `n>=2` and the putative equation
`x*x+1=n*(n+1)*y*y`. It derives `y>0`, `n*y<x` and
`2*x<(2*n+1)*y`. The actual internal truncated difference
`v=(2*n+1)*y-2*x` therefore satisfies `0<v<y`. Its new root is the
absolute difference of `(2*n+1)*x` and `2*n*(n+1)*y`; no sign of that
inverse root is presumed. A direct additive identity proves the same
negative norm at `(u,v)`, and the norm bounds `u<=(n+1)*v`.

`consecutive_ne_negative` uses genuine internal order induction on `y`,
with the bounded root invariant
`forall x <= (n+1)*y, x*x+1 != n*(n+1)*y*y`. The predicate is bounded
Delta0 and is admitted to the explicit IΣ1 induction API by definability.
No external natural-number induction, Pell classification, sign oracle,
standardness assumption or supplied minimal counterexample is used.
Checks preserve the actual `n=x=y=1` counterexample, so the restriction
`n>=2` is not silently strengthened or omitted.

These are arithmetic exclusions for the required factor shapes. Signed
pair multiplication and extraction of unit factors, the literal
`ArithmeticExpression.splitNatural` evaluator binding, and the complete
maintained-polynomial soundness/PA/HA endpoint remain separate work.
No source certificate, desired index or cofinal witness occurs here.

The two imports are exactly `Foundation.FirstOrder.Arithmetic.IOpen.Basic`
and `Mathlib.Tactic.Ring`. The approved zero-refresh DAG contains 86 custom
modules, all Foundation, with 344 custom artifacts. Its 37 explicit
external boundary names have 111 total artifacts: 37 primaries and 74
companions. All 455 actual first providers were authenticated, including
implicit Init and the complete explicit package search order. The accepted
Gcd ROOT provider supplies these unchanged prerequisites; the Gcd module
itself is not imported. Existing source/object/trace provenance
qualifications are retained. No Foundation or other prerequisite was
rebuilt, and no fresh dependency-closure claim is made.

Every attempt used pinned Lean 4.32, `-M6000 -j1 -DElab.async=false`, one
thread, default heartbeat bounds, a 512MiB reserve guard and fresh regular
outputs. Both source inputs were snapshotted before each attempt, including
Checks when the main failed. Attempt 1 rejected the missing `noncomputable`
annotation on the private absolute-difference helper, causing subsequent
realization/simplifier failures; three linter notices were also retained.
Attempt 2 rejected only the associative/commutative normalization in the
second order branch of the magnitude-square identity. Attempt 3 supplies
the explicit AC rewrite lemmas and passes both leaves. All three attempts,
their commands, snapshots, drivers, logs, timings and authentication are
preserved. No public statement, premise, import or resource cap changed.

The final main/Checks peak RSS is 1,828,152/1,783,440 KiB. Postflight checked
1,415 paths and retained 726,179,840 free bytes. The durable freeze rechecked
7,039 observations across 2,157 paths and retained 703,524,864 free bytes.
No reserve guard was rejected. Immutable plan/proposal references avoid
per-attempt inventory copies. Durable terminal evidence is stored as regular
hardlinks with exact paths and bytes preserved; new authentication and
manifest files are ordinary writes. No source or proof object was rewritten
by that storage step. No accepted file, shared object, display or Git edit
was made.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticNegativeNorms | 33d86c09729bda75824591bf840e67ae13d9bf81ed09a5d0f46d2232cc1a63a6 | ce7f3bb2e5b6f93001208670d0249361ccc9fb2fc9cdbe8d9e55abe3be8cd2ae |
| ArithmeticNegativeNormsChecks | 9aec6ab34ef3a30510d21b201d62bf1447111ed20d0f34512661ffbd314ba9c0 | 58dd05ef646a8adcfb41dce9ea0e979612ed0b1db58da0276aca378e27c9a519 |

Final provider: `/tmp/arithmetic-negative-norms-author-6boj1rv7/lib`.
The [replay packet](arithmetic-negative-norms-replay.json) is
`852a4e8352b9176a5fed1456099e5676e4a53b3d26ab283b93d1eb02c1a21380`.
The [33-file manifest](arithmetic-negative-norms-author-replay/FILES.json) is
`d5cac0dc47f445a8989678f552e5058d052d50d822b2715ce7dcc995149280d0`.
Executed driver SHA:
`40e02bce62830fd54df5bb97ece27bc85780d81906ca3012655370d3f5babfdc`.
Freeze script SHA:
`a1b085111cc73be2d6306202f33fa80e1c87238bf6e4fa0edc2ce0047cc16450`.

The controller's earlier challenge checked the ordinary descent arithmetic
and emphasized the explicit bounded-induction strength. This receipt does
not claim an independent source, compiler or provenance review.
