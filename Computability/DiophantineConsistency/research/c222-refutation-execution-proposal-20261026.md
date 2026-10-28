# Actual C222 refutation execution: next scoped checkpoint

26 October 2026. Read-only proposal; root owns any new
`ArithmeticProofWordEnumPerm222` and Checks implementation. No proof source,
Lean invocation, prerequisite build, shared cache or Git change was made for
this proposal. The separate independent History replay has passed and is
frozen in `reviews/arithmetic-proof-word-perm222-peer.md`.

I read the complete current History, Fair and EnumRun modules, actual Block
`eval_ax` and command-step AX definition, working/full-state encodings, Cantor
projection contracts, and the existing represented-totality sentence and
arithmetic completeness pattern. The root's one-command reset proposal has
no mathematical finding. It closes a real missing premise: History's
contract quantifies over top and stack with both control registers zero;
Fair's `halts_of_word` requires all encoded working states, including dirty
control registers and false cache1.

## Exact finite bridge

Use only two direct imports:

```
DiophantineConsistency.ArithmeticProofWordPerm222
DiophantineConsistency.ArithmeticEnumFairPerm222
```

Let `rest code := ArithmeticProofWordPerm222.refutationWord code` and
`resetWord code := ArithmeticCommandBlockPerm222.axWord 1 0 0 (rest code)`.
The API argument order is c,x,y; the physical instruction fields are y,x.
Both supplied fields are zero, and the physical command tag is 1+3=4.

All numeric representation statements may remain universe-polymorphic.
Execution theorems below retain `{V : Type}` (Type0), `ORingStructure V`
and the actual IΣ1 model instance, as required by the selected fixed rho8
circuit. Let `h` be exactly
`ArithmeticHistory222.checkDef.val.Evalb ![code,1]`.

1. Prove every internal `w` decomposes as
   `stateValue (first w) (first (second w))
     (first (second (second w))) (second (second (second w))) = w`.
   Unfold stateValue and use cantor_projections three times. No code-validity,
   positivity, standardness or register-range assumption is necessary.
2. For arbitrary top,S,d,hcache, literal eval_ax gives
   `evalValue (resetWord code) (stateValue top S d hcache)` equal to
   `evalValue (rest code)
     (stateValue (gateValue d hcache 1)
       (axStackValue d hcache hcache 1 d top S) 0 0)`.
   The gate and all newly pushed formulas can remain completely uninterpreted.
   History.refutationWord_halts accepts any new top and stack. This includes
   hcache=1, d=0, gate-label collisions and arbitrary old stack contents; AX
   does not test the old cache like NIP does. Thus obtain
   `∀ w : V, evalValue (resetWord code) w = 0` under h alone.
3. The reset word is a successor, hence nonzero. Its raw predecessor is
   `cantor 4 (cantor 0 (cantor 0 (rest code)))` after the literal arithmetic
   simplifications. Cantor.components_le, or first_cantor plus
   projections_spec, proves `4 ≤ resetWord code - 1`. No closed numeral
   expansion or general monotonicity estimate is needed.
4. Apply actual `ArithmeticEnumFairPerm222.halts_of_word` with initial
   candidate4, arbitrary initialWork, the proved nonzero/lower-bound facts
   and the proved universal working-state halt. Export:

```
theorem check_halts_enum {code : V}
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1])
    (initialWork : V) :
    ∃ time, ArithmeticEnumRunPerm222.run time
      (ArithmeticEnumStepPerm222.liveValue 0 4 initialWork) = 0
```

No supplied universal-halt, scheduler fairness, word-contract or runtime
premise belongs in this final theorem. Those are all discharged by the
accepted lemmas and this actual reset. This is candidate4 and arbitrary work;
it does not assert termination from a scheduler counter already above the
constructed candidate.

A fixed Σ1 reset-word graph is useful but optional for this checkpoint. It
can bind rest by refutationWordDef, then form three exact Cantor pairs:
`p=P(0,rest), q=P(0,p), raw=P(4,q), word=raw+1`. This reuses pairDef and does
not require a new circuit language or recursor. It is externally fixed,
noncomputable syntax for the same reason as refutationWordDef. Nothing in
the closed theorem below requires exposing this auxiliary graph.

## Literal closed arithmetic theorem

Use a literal `ArithmeticSentence` with the existing exact graphs:

```
∀ code, !ArithmeticHistory222.checkDef code 1 →
  ∀ w, ∃ initial, !ArithmeticEnumStepPerm222.liveDef initial 0 4 w ∧
    ∃ time, !ArithmeticEnumRunPerm222.runDef 0 time initial
```

It has no free parameter or metatheoretic proof predicate in its syntax.
The actual graph realization lemmas and check_halts_enum prove its truth
in every Type0 IΣ1 model. `LO.FirstOrder.Arithmetic.complete.{0}` then gives
`𝗜𝚺₁ ⊢ refutationExecutionSentence`; ordinary theory weakening gives the PA
version. This exact completeness lemma and the working example in
ArithmeticCommandRunPerm222 are already in the selected closure. The
external metatheory may use its usual classical axioms; this is actual
object-language IΣ1 theoremhood of a conditional execution statement, not
an HA proof or a semantic truth assumption added to its hypotheses.

Suggested focused checks: arbitrary dirty d/hcache including1; the zero
working code; nonzero/lower-bound for every code even if rejected; actual
check graph supplies the entire endpoint; sentence closedness/type and both
IΣ1/PA provability statements. Optional standard-Nat conversion can use
EnumRun.run_zero_iff_native_none directly, but importing actual CProv222 or
reproving its existential adapter is unnecessary here.

## Authenticated inputs and remaining boundary

The frozen companion cache plan records 140 custom modules, including95
Foundation,425 object/companion artifacts and38 external names. Relative to
the History precompile135-module cache, it adds the accepted new History
main, CommandFetchPerm222, EnumStepPerm222, EnumRunPerm222 and FairPerm222.
All135/122-overlap sources, imports and object records agree exactly; there
are no alternate mismatching providers. The selected new main objects are:

- History: `/tmp/proof-word-perm222-controller-peer-dbt343z4/lib/DiophantineConsistency/ArithmeticProofWordPerm222.olean`,
  `f8edc491dc3e147ce5f559424fda38a69f5686e046422b7f8d06a1d5b860b46b`.
- Fair: `/tmp/fairperm222-independent-l0q7y63z/lib/DiophantineConsistency/ArithmeticEnumFairPerm222.olean`,
  `29c1b77965bd3b4dcacd1c5b40df08f109310996df81a55a75d80c19d70da587`.

The plan reauthenticates7,896 repeated observations (910 distinct path/digest
pairs), including the accepted independent Fair evidence and source snapshots;
its graph is fully reachable and topologically ordered from the two imports.
No old C254 compiler/word semantics are used. The initial plan's tentative
target name was corrected to root's ArithmeticProofWordEnumPerm222 before
freeze; both metadata drafts are preserved under /tmp. No proof code changed.
Any authorized future replay should compile only its two new leaves in a
private overlay, use pinned4.32 -M6000 -j1 -DElab.async=false, retain failed
attempts and snapshots, and check the512MiB reserve before each invocation.

This checkpoint would establish actual represented C222 refutation → actual
permuted enumeration halt and its closed IΣ1/PA conditional. It would not
supply an internal source-theory refutation → C222 translation, an internal
Enum-to-215 simulation, the reverse scheduler proof-state invariant, a
Pell/equation internalization, or the requested final HA equivalence. Those
remain separate substantive obligations.
