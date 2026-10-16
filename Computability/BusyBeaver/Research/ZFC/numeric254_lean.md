# Exact transport into the original numerical calculus

16 October 2026. Two new Lean modules close the finite proof adapter from
the named primitive-falsity calculus to the **original four-tag numerical
calculus**, shared by the published 254-state and attributed public 253-state proofs:

- [`Numeric254.lean`](../../Lean/BusyBeaver/ZFC/Numeric254.lean) defines the
  numerical constructors, all eight original logical rows, the entire
  C/G/vacuity bundle and its gate, and the twelve-constructor `NumThm`.
- [`NamedNumeric254.lean`](../../Lean/BusyBeaver/ZFC/NamedNumeric254.lean)
  defines the named encoder, proves derivation transport for all thirteen
  `Tarski.Thm` constructors, and records its exact refutation corollary.

The definitions are an attributed port of Jeff's `Codes254.v`, `Thm254.v`
and `Enum254.gate`, at busy-beaver commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. Mira-Cult designed the machine;
Jeff supplied its verification. These logical sources are unchanged at
mira-emmy's public 253-state pin `0d544f2a2e3c18f12278441a74b7879f31cbe856`.
The new files preserve that attribution and do not relicense the upstream
snapshot. This work does not construct or claim authorship of a new machine.

The numeric syntax is exactly

```text
P(a,b) = triangle(a+b)+b
Imp(a,b)=4P(a,b)    Rel(i,j)=4P(i,j)+1
All(i,a)=4P(i,a)+2  Eq(i,j)=4P(i,j)+3
F=1=Rel(0,0)       Imp(0,0)=0.
```

Negation, existential quantification and conjunction use implication to F,
as in the original program. The bundled axiom is
`(C ∧ G) ∧ (vRel ∧ vEq)` under precisely `c≠a` and `c≠b`; its numerical
proof rule permits `a=b`. The actual gate emits0 on failure, and `gate_thm`
proves both successful and failed gate outputs belong to `NumThm`.

`Numeric254.classical` is constructed from the actual numerical MP/rho8/rho6
rows. The existing generic finite rho8 certificates yield K/S/Peirce for
all natural parameters, including0. K/S and original rho6 yield numeric
ex falso. Classical conjunction projection then derives the two gated
atomic vacuity families **from the full bundle**. They are not additional
constructors of `NumThm`. No semantic assumption that F is false is needed
for these syntactic derivations.

The named encoder maps `NF.bot` to F, preserves implication and universal
quantification, and uses the displayed numeric membership/equality
constructors. Thus `bot` and `rel00` deliberately collide at code 1. The
named formula `bot→bot` instead has code 16; runtime truth 0 is a separate
axiom. Neither injectivity nor a decoder is asserted.

The general `NamedNumeric254.transport` theorem translates a named
`Thm Ax f` derivation, given an explicit proof that each named theory axiom
has a numerical proof at its encoded value. All rule cases are checked;
rho8's named order `c,u,a,b` becomes numeric order `a,b,c,u`. The vacuity
cases use the projections above, with their unchanged gates.

For the specifically defined theory

```text
Q(f) := Numeric254.NumThm (NamedNumeric254.encode f),
```

that axiom premise is discharged by the identity function. Therefore the
new closed theorem is

```text
Tarski.Thm Q NF.bot ↔ Numeric254.NumThm 1.
```

The forward implication is proof transport. The reverse implication makes
the given numerical proof an axiom of Q; this does not assume a theory
calibration. The predicate Q is explicitly the theory of encoded numerical
theorems. Identifying its models or refutations with SIR or ZFC is still a
separate obligation.

One concrete consequence is the named irreflexivity sentence
`all0 (rel00→bot)`. Its numerical image is610, and numeric GEN applied to
identity at F proves it belongs to Q. `ir_code`, `ir_in_Q` and `named_ir`
check all three parts. This explains how the intended named theory gains
IR despite the deliberate falsity/atom collision; it does not permit an
unconditional semantic replacement of the atom in an arbitrary relation.

Both modules and a caller in each direction of the refutation equivalence
passed with the **explicit absolute Lean 4.32.0 compiler**
`/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`.
The binary's `--version` was checked before every final command. The final
module checks took 0.41 and0.33 seconds, and the 23-theorem signature/axiom
audit took 0.28 seconds. Compilation emitted no warnings. The numerical
basis and IR facts use no axioms; conjunction projections and transport
use `propext` through the existing finite-hypothesis deduction machinery.
The gate proof additionally depends on `Classical.choice` and
`Quot.sound`. No admission, custom axiom, `native_decide`, or unchecked
external computation occurs in either proof module.

A separate finite source-contract check compares all 20 nonrecursive
numerical definition terms and all 12 inductive constructor signatures
against the pinned Coq sources, modulo binder renaming. It also checks the
triangle recursion and the two equality tests/zero result of the gate.
The complete C/G subterms match; their correctness was not inferred merely
from the much smaller vacuity projection used by transport. This source
comparison is a reproducible external audit, rather than a theorem about
Coq source text inside Lean.

[results/numeric254-verification.json](results/numeric254-verification.json)
records exact commands, actual per-command compiler versions, source
identities, all audit results, the checked caller and the source-contract
checker text. Dependencies were reused from the explicitly pinned,
source-verified cache; no `Boot253` or Coq build was run. The new modules
were compiled serially into `/tmp/zfc-numeric254-check-cu5sp1ud`.

No total decoder, semantic truth theorem for runtime F, Q/SIR/ZFC
calibration, enumerator soundness/completeness, program or binary
simulation, internal consistency endpoint or new state bound follows
from this adapter alone. It preserves the complete original frontend;
it does not substitute the experimental ternary, Bottom3, PSC, EPSC or
unary-rule presentations.
