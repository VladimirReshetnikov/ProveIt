# Logical-engine completeness and a retained-engine PSC control

Deleting the equality rows from the published logical engine removes its
implementation of variable instantiation and bound-variable renaming. A
shorter nonlogical theory does not make those operations unnecessary. The
safe current control retains the entire published engine and changes only
the theory emitter. A genuinely equality-free implementation can instead
use full capture-avoiding instantiation and a standard quantifier-introduction
side condition, as in the accepted source08 reference checker.

No new Lean proof, complete compact replacement, binary simulation or
internal ZFC endpoint is claimed here. The original pinned sources were
read as data; no Coq code was run. The new files do not alter any existing
candidate, generator core or Lean module.

## What the original equality mechanism supplies

All upstream paths below are relative to `lib/jeff-busy-beaver-zfc254`, pinned
at `297ab8df7e5de329605c3875b4934643b371a5e3`.

* `ZF/m254/coq/logic/Thm254.v:9–21` defines the actual code calculus:
  truth0, MP, GEN, rho1–rho8 and the gated bundle.
* `Codes254.v:103–110` spells out the rows. Rho1 is existential equality,
  rho7 is Euclidean equality, rho3/rho5 transport membership arguments.
* `ZF/stdzf/coq/L1_LMeta.v:54–61` obtains equality reflexivity using
  Euclidean equality, equality-vacuity, existential equality and old B6c.
  Its equality transport and formula induction appear at `:70–86,195–233`.
* `L1_LMeta.v:247–257` derives specialization to a **different** variable
  through Leibniz transport, existential equality at line255, vacuity and
  B6c. Alphabetic variance at `:260–276` depends on that specialization.
* `ZF/stdzf/coq/Std_alpha.v:172–217,276–280` extends this to proper free
  substitution and capture conditions. `Std_H.v:242–290` transports ordinary
  natural deduction: its AllE case uses that specialization, and AllI uses
  freshness and alphabetic variance.
* `ZF/m254/coq/logic/Comp_Prop254.v:59–76` derives explosion and relative
  double-negation elimination from original rho6. Its `lprov_thm` at
  `:115–136` imports all the original logic, including equality/vacuity.

Thus upstream proves far more than Boolean truth of the retained formulas.
Its completeness bridge cannot be inherited after removing equality rows.

## Two independent obstacles to small quantifier-only repairs

`logic_engine_controls.py` records finite algebraic diagnostics. These are
proof-system counterinterpretations, not ordinary membership structures.
They make no assertion that the actual C/G set-theory bundle is modeled.

First, on a reflexive symmetric but nontransitive three-world path
`0~1~2`, let quantifier0 be its universal box and every other quantifier
be identity. Use genuine false Bottom and material implication. All Boolean
truth subsets validate QI, original B6c, same-variable specialization,
commutation and the proposed ax467 formula. Let Rel(0,0) be true at worlds0,1
and false at2, and all other atoms be false. Fresh atomic membership-vacuity
also holds. Nevertheless at world0

```
All(0,A) → All(0,All(0,A))
```

fails. Adding only same-variable specialization does not close this gap.

There is an even simpler, independent cross-variable obstacle. Let every
quantifier be identity, use primitive false Bottom, and independently assign
Rel(0,0)=true and Rel(1,1)=false. Every usual quantifier-only schema remains
valid, including specialization, idempotence, commutation and ax467; atomic
fresh vacuity holds. But the first-order valid formula

```
All(0,Rel(0,0)) → Rel(1,1)
```

is false. No collection of such atom-parametric quantifier schemes can
supply the missing relation between differently named atoms. There must be
actual substitution/renaming, appropriate atomic transport axioms, or an
equality mechanism implementing it. This control has a genuine primitive
Bottom; it must not be conflated with the relative F=Rel(0,0) interpretation
or extended to a particular nonlogical theory without checking its axioms.

The earlier constant-true-quantifier interpretation remains a countermodel
for the new incomplete PSC skeleton. The script reruns the actual C/G
negative control: all32 payload assignments give C=false,G=false,V=true,
so it **does not** model the frozen252 C/G bundle. Its outer existential
wrappers matter. The frozen candidate remains uncalibrated, not refuted by
this particular counterinterpretation.

## The precise Metamath ax467 opportunity

The primary [ax467](https://us.metamath.org/nfeuni/ax467.html) page describes
replacement of same-name specialization, old B6c and commutation while retaining
**ax-5o**, generalization and propositional logic. Its ordinary-negation
reverse derivations are linked there. [Ax-4](https://us.metamath.org/nfeuni/ax-4.html)
explicitly distinguishes same-name specialization from general substitution
and explains the role of equality for a different instantiating variable.

The retained [ax-5o](https://us.metamath.org/nfeuni/ax-5o.html) is

```
All(x, All(x,A)→B) → (All(x,A)→All(x,B)).
```

It is stronger than merely our QI row. Setting B=All(x,A), its quantified
antecedent is a generalized tautology, so MP yields positive introspection.
The path countermodel above falsifies this protected scheme while validating
QI and ax467. Therefore that Metamath basis cannot be imported as a literal
replacement of just the current B6c/commutation rows. Even the full protected
basis still needs cross-variable transport. The separate relative-falsity
issue is documented in `dual_quantifier_gap.md`.

## A concrete complete equality-free target

A conservative reference target is the exact calculus already specified by
batch144 source08: genuine Bottom, K/S/full classical contraposition, MP,
GEN, and these two schemas:

```
UI: All(x,A) → A[x:=y]      (capture-avoiding free substitution)
UD: All(x,A→B) → (A→All(x,B)), provided x is not free in A.
```

This is the ordinary complete Hilbert presentation, with closed nonlogical
PSC instances. It avoids equality constructors but pays for free-variable
checking and capture-avoiding substitution. Its accepted Python checker is
an executable specification, not a verified small machine or a Lean proof
of that Hilbert presentation. A theorem-level capture-avoiding substitution
rule plus same-name UI can derive full UI by substituting in the free
consequent of `All(x,A)→A`; the antecedent's x occurrences are bound. That
is another honest implementation interface, not a free arithmetic operation
on formula codes. No smaller complete implementation is established here.

The existing Lean starting point is stronger and reusable now:
`Logic/FirstOrder/Lean/FirstOrder/Calculus.lean:33–55` defines actual natural
deduction, with `P_allE` performing `rename (inst k)` and `P_allI` shifting
the context. `Prov_rename` at `:173–229` and the syntax equations in
`Fol.lean` already handle variable renaming and capture structurally.
`Completeness.lean:1082–1099` proves relative completeness for every sentence
theory, with arbitrary finite contexts/targets.

The formal bridge should define the chosen finite proof objects and prove
that checking produces `BProv` derivations. In the other direction it must
translate the quantifier rules, including the fresh-variable condition on
AllI and the actual substitution in AllE. For a wholly equality-free engine,
either prove completeness of that subcalculus or prove equality erasure of
full proofs using two-sided observational profiles. Existing completeness
for a calculus with equality does not automatically prove completeness of
its equality-free rule subset. Retaining the equality engine is the present
control that avoids this extra deletion argument.

## Measured full-engine PSC control

`full_logic_psc_control.py` first matches the original281-state Wade table
and the full old AX symbolic specification. It retains **all9** logical
outputs (GEN plus rho8 through rho1), both atomic vacuity components, original
four formula tags, original relative F and NIP target. Only C/G theory
emission is replaced by the fresh k=c+2 PSC adapter. Both an additional
separate IR row and no extra IR row are measured. There is no further search.

The independent curried six-fresh-label adapter check is extended to matrices
with actual equality atoms: all17564 cases pass. All72 small register tests
for copying c then adding2 preserve c/other registers and push the old current
formula correctly. Exact expanded macro words are checked across the seed2
Re-Pair transformation.

| Compilation | Decision | Framework | Working |
| --- | ---: | ---: | ---: |
| Pinned original program | 219 | 62 | 281 |
| Full logic + PSC, ordinary sharing | 221 | 62 | 283 |
| Full logic + PSC, fixed Re-Pair seed2 | 217 | 62 | 279 |
| Full logic + PSC + separate IR, ordinary sharing | 227 | 62 | 289 |
| Full logic + PSC + separate IR, fixed seed2 | 221 | 62 | 283 |

There is a specific reason to measure the no-extra-IR variant. Upstream
`Comp_Bundle254.v:91–95` derives the comparison theory's IR from the closure
of Wn(Rel(0,0)), whose tau code is F→F, using only `thm_I`. This translated
IR is already available to the retained logical engine; an additional emitted
row is redundant for that proof strategy. The intended comparison still
includes IR, which validates the falsity alias in soundness. It is not a
claim that raw PSC itself proves IR. Source08 calibrates the equality-bearing
PSC+IR comparison by its sandwich argument.

Adapting the upstream proof still requires the new PSC schema/parameter
translation, vacuity projection, altered emitted-row stack discipline,
enumerator proof and binary compiler simulation. None has been proved for
these tables. The measurement identifies a legitimate complete-front-end
**control specification**, not an already certified changed machine. Every
output is a partial named table with the same sole missing `1.inc/read1` row;
no new literal total table is installed.

Reproduce offline, assertion-enabled, with no proof-assistant build:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/logic_engine_controls.py \
  --output /tmp/logical-engine-controls.json
uv run --no-project python Computability/BusyBeaver/Research/ZFC/full_logic_psc_control.py \
  --scratch /tmp/zfc-full-logic-psc --output-evidence /tmp/full-logic-psc-control.json
```

The committed evidence is `logical-engine-controls.json` and
`full-logic-psc-control.json`. Generated tables and unchanged licensed Wade
backend copies remain in outside scratch. No sub254 endpoint is claimed.
