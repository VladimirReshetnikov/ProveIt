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

The subsequent [finite-sort model](typed_countermodel.md), delivered in
`47f3a36029`, settles a stronger question: every emitted reduced C/G bundle
is valid with target false, using either quantifier row. It also models the
offset PSC wrapper and same-variable specialization. The original complete
equality engine and the controls retaining it are outside that argument.
Ordinary equality-free PSC/CP/GIC calibration survives; a complete replacement
frontend or the original engine is needed to implement it.

## Batch 147: complete specification and ternary Bottom

Source 16 of the closure-kernel report (`9439d775aa`) supplies another complete
ordinary Hilbert checker: K/S/C, arbitrary capture-avoiding cross-variable UI,
QD with its free-variable side condition, MP, theorem GEN and a closed PSC
schema constructor. Every accepted conclusion is constructed; arbitrary
assumptions are not accepted. The ordinary completeness argument provides a
reference for future refutation transports. The checker has not been compiled
into any of the source's 250/251/252 tables.

Its ternary primitive-Bottom codec now has Lean round-trip, canonical
injectivity, label-bound and ordinary semantic-preservation proofs; see
[bottom3_codec.md](bottom3_codec.md). These address formula representation,
not UI or proof enumeration. The finite-sort countermodel continues to
validate the source's reduced C/G/V word after the member-code offset changes.
The genuine Bottom change therefore cannot repair that calculus by itself.

The proposed total theorem constructor (invalid local tests return Truth)
remains an unimplemented compression design. It needs both a theorem-validity
invariant and surjectivity onto refutations, including normalization and
capture-avoiding substitution. The source's finite Horn encoding of any fixed
machine similarly gives an ordinary consistency/nonhalting equivalence, but
its clauses contain the original computation; interpreter and clause-printer
costs must be counted before it can save states.

## Batch149: composite collisions and two complete references

Source19 strengthens the diagnostic boundary: fresh instantiation, injective
renaming and **both signed atomic** instantiation schemas still do not imply
instantiation of a composite formula at an already occurring variable. Its
two-bit interpretation uses `R(i,j) = (i != j and s(i)=s(j))`. For distinct
x,y,z the matrix `((Rxy<->Rxz)<->Ryz)` is universally true in x, whereas replacing
x by y makes it false on every assignment. This is a logical counterinterpretation;
it is not asserted to validate PSC. The finite-sort result remains the
separate theory-specific obstruction.

Two new complete ordinary reference interfaces handle the missing collision:

- Source18's locally nameless Hilbert checker verifies explicit open/close/plug
  witnesses, permits opening to an existing free name, and checks the freshness
  side condition as a close-to-self identity. Its strict binary proof format
  has a fair shortlex search. The delivered Lean binding theorems cover finite
  syntax/scope identities, not the Python verifier or its semantics.
- Source19's signed tableau checker uses one shared PSC template with three
  matrix calls. It compares atoms after evaluating environments, permits equal
  parameter values, and can insert schema instances after fresh witnesses are
  allocated. Freshness covers hidden map values as well as visible stacks.
  The ordinary soundness/completeness argument includes fair revisiting of old
  universals and late parameterized AX instances. The codec is total and the
  refutation entry has a fixed Bottom target.

Their finite tests pass; neither has a compiled state cost. Their illustrative
accepted logical theorems are not PSC contradictions. Theory calibration,
proof-language correctness and actual binary simulation remain distinct steps.
The source18 destructive-read audit also shows why an abstract schema
permutation is insufficient as a compiler contract:12 of24 rho8 permutations
read the fourth stream parameter more than once. Source11's retained permutation
has the safe single-read invariant.

Source19 separately reaches **268 working states** while retaining all original
logical/equality rows. It changes only conjunction layout in the theory bundle,
then compresses that revised exact word. Relative conjunction commutation and
association are provable for arbitrary falsity alias F; GEN/QI and implication
congruence lift both directions through unchanged contexts. This is a valid
ordinary source bridge, still lacking a checked proof-code certificate.
The4,533-pair operation certificate covers revised217→206 decision nodes, plus
62 framework states. All53,760 grammar/layout choices and8,192 PSC control
choices reproduce. The full-equality PSC controls reach278 without explicit
IR and282 with IR; these improve the fixed measurements above without giving
new binary/calibration proofs. See the complete
[intake149 reconciliation](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch-149-binding-certificates-and-shared-substitution).

## Batch 150: three further complete interfaces

Reviewed sources 20–23 add three concrete complete reference interfaces:
source 20's captured-closure tableau keeps the matrix namespace separate
from private template labels; source 21 bounds the matrix environment to
[x,y,p,q] using its independently calibrated EPSC2 theory; source 23 replaces
implication/falsity/forall syntax by R and quantified NAND Q, binding both
children of Q. Each public checker reconstructs only its intended theory
roots, checks all required branches and enforces fresh witnesses. Their
ordinary completeness proofs and finite tests are accepted at intake; no
new binary implementation is supplied for these frontends.

Source 22 instead retains a complete K/S/contraposition Hilbert kernel and
implements a native closure production. Its unary protected-witness version
removes a separate matrix argument, while adding a bound parser and shared
edit passes. The equivalent basic-rule and axiom versions provide controlled
comparators. Keep their codecs separate: source 22 has bijective Bottom0,
whereas source 20's exceptional Bottom1 codec also normalizes a Truth0 alias.
Neither is identified with the existing machine by the ordinary theory proof.

The source 23 old-word control remains 269 states after independent full-cost
repricing of all 6,720 distinct recipes; its 960/6,000 advertised searches
originally ranked only decision nodes. The retained source 19 word already
has a 268-state control. Every future comparison must charge the actual
compiled dispatcher depth, initialization, arithmetic, matrix generation,
branch storage and freshness. The four detailed dossiers and original
recovery commands are in the closure-kernel host's batch 150 section.

Separately, `Tarski.complete` now proves completeness of the full named
primitive-falsity calculus without supplied classical-basis hypotheses.
The attributed [107-certificate Lean port](lukasiewicz_basis.md) derives
K/S/Peirce from rho8 and ex falso from original rho6. This closes the
specific gap in the imported conditional theorem, while leaving numerical
syntax, relative runtime falsity, theory emission, enumeration and binary
simulation as distinct obligations. It does not repair the reduced systems
refuted by the earlier fixed-slot and finite-sort countermodels.

## Batch 151: a small equality formula and finite carriers

The [source-24 review](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-151-source-24.md)
accepts a four-node outgoing equality proxy and a reserved-zero falsity
translation. Both membership positions retain full variable transport.
A local zero binder inside the equality macro is safe; globally forbidding
GEN0 alone does not protect the distinguished point from other binder-producing
operations. The package's translator is a finite diagnostic interface, while
its translated proof checker remains a specification. Its actual strict EPSC
proxy control is 288 states, with the full variable dispatcher charged.

The same source emits a complete SK term and a one-constant version for the
attributed public 253 table. The three-equation/inequation carrier retains its
large ground payload: 192,272 BCL bits. No binary evaluator cost is supplied.
The generic parser-domain claim is false for a negative start label; the host
preserves the exact native-halt/compiled-loop counterexample and limits the
claim to valid nonnegative starts. The frozen start-zero payload reproduces.

The [source-25 review](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-151-source-25.md)
checks a complete genuine-Bottom Hilbert reference with capture-avoiding
instantiation and an EPSC/EFPC selector. It also verifies a narrow modal-list
counterexample against the primary paper: omitting reflexivity allows constant
true box/false diamond. The original quantifier and equational presentations
exclude that valuation; their main interpretation theorem is unaffected.
Neither reference is the numerical algorithm of the measured machine controls.


## Batch 152 frontend comparisons

Sources 28, 29, 31 and 33 of the closure-kernels host (arrival `da6dabcd89`)
offer complete ordinary reference algorithms with different implementation
costs: signed names with explicit contraction; ground epsilon plus finite
Boolean unsatisfiability; default-last four-slot EPSC2 and dense positive-scope
quantified-NAND coding; and the SR₂⁺ finite-pool tableau with one shared world
witness. None has a newly compiled complete binary frontend. Local finite
transducer counts and syntax-bit comparisons are not whole-machine state costs.

The incoming description of code 0 as syntactically closed is corrected in
host remark 152.1: `Rel 0 0 → Rel 0 0` has free variable 0 but is semantically
true, and the stated `c+2` freshness offset survives. Historical claims that
the concrete Lukasiewicz basis, named completeness or nonempty-model repair
are missing now overlap checked project declarations. Archived Lean adapters
were independently rebuilt without installing their old patches. The complete
numeric theory calibration and binary endpoint are still separate tasks.
