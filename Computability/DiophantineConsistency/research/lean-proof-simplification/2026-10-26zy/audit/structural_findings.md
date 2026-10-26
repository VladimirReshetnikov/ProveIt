# Structural findings: derive computability from the supplied enumerator program

Pinned source: `3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114`.

## Retained proposal S1: invert the proof dependency

`Computability.lean` currently proves primitive recursiveness independently of the
explicit scalar program. Its private chain begins with `stateEquiv` and the six
register projections (lines 17–50), continues through arithmetic constructors and
`pr_rawStep`/`pr_enumStep` (through line 240), then supplies `pr_boundedRun`
(lines 246–249), `refutationInputs_re` (294–308) and
`haltingTest_natPrimrec` (314–318). Meanwhile,
`DirectScalarEnumerator.lean` builds an actual
`DirectEnumerator.program : ScalarPRCode.Realizes haltingTest` (267–270), and
`ScalarPRCode.primrec` already certifies every supplied code (line 36 onward).
The direct scalar module imports Computability, so the immediate one-line reuse
would create a cycle. Split the semantics first, then reverse that edge.

The mathematical certificate is simply:

```lean
theorem natPrimrec {f : ℕ → ℕ} (p : ScalarPRCode.Realizes f) : Nat.Primrec f :=
  p.val.primrec.of_eq p.property
```

This is a proof elimination at the project level: the project already maintains
the executable program and its correctness, so a second arithmetic PR closure
chain is unnecessary. It remains useful even assuming all old fun_prop closure
rules and shared enumerator frontend proposals are applied.

### Concrete module boundary

1. New `EnumeratorSemantics` holds the existing definitions `boundedRun`,
   `initialState`, `refutationInputs`, and `haltingTest`, together with their
   iteration/halting equivalences. Retain the existing private encoding and
   decidability instance because `haltingTest` uses `decide (boundedRun ... = none)`.
2. `DirectScalarEnumerator` changes only its second import, from Computability to
   EnumeratorSemantics. Every subsequent source line is unchanged.
3. `Computability` imports DirectScalarEnumerator, proves
   `haltingTest_natPrimrec` directly from the supplied program, retains the vector
   conversion, and proves `refutationInputs_re` by searching for `haltingTest t = 1`
   rather than for `boundedRun t initialState = none`.

Dependency order:
`EnumeratorSemantics -> DirectScalarEnumerator -> Computability -> Bridge`.
DirectScalarEnumerator separately imports DirectScalarArithmetic -> ScalarPRCode;
those modules do not import Computability. EnumeratorSemantics imports the same
lower BusyBeaver EnumPerm semantics as the old Computability, so no reverse
DiophantineConsistency edge is introduced.

### Interface and executable-data conditions

All existing public theorem statements and public definitions can retain their
names and source bodies. The supplied scalar program's source is unchanged except
for its import. Its construction remains data-valued; nothing is reified from a
Prop proof or selected via classical choice. The new dependency makes
Computability's trusted derivation use the existing scalar program. This can
increase its import/elaboration burden, so source simplification is not a measured
speedup. Retaining both pipelines as an independent test is a deliberate alternative,
but then move the redundant derivation to an optional regression/audit module.
Do not keep it in the maintained theorem dependency closure while counting it as
removed.

Only Bridge.lean uses `refutationInputs_re` in production, and it explicitly
imports Computability. No production caller outside Computability uses the two
primitive-recursiveness theorems; checks/ZFCAxioms.lean audits the named public
endpoints. ExplicitZFC imports ZFCFromProgram -> Bridge, so it still sees those
endpoints after the change. All public semantics remain re-exported by Computability.

### Exact deliverables and evidence

`patches/S1-realizer-dependency-inversion.patch` supplies a complete
three-file source proposal, with full candidate files under `proposed/S1/`.
Current source total (Computability + DirectScalarEnumerator) is 608 physical
lines; proposed total including the entire new semantic module is 392, a 216-line
reduction **relative to the actual pin only**. This is not a marginal number against
the nonexistent unique counterfactual implementation of all 41 prior packets.
No runtime improvement is claimed.

Freshly compiled the exact pinned ScalarPRCode source copied into the prototype
workspace, then compiled `RealizerPrimrecBridge.lean` against Lean 4.32.0 and its
Mathlib imports. The natural certificate uses `[Quot.sound]`; the vector bridge
uses `[propext, Classical.choice, Quot.sound]`. There are no admissions. First
bridge attempt omitted Mathlib.Computability.Primrec.List and failed only on the
vector names; after adding that exact import, the complete bridge compiled.
Final success is in `bridge-final-log.json`; first-attempt history is retained in
`compile-log.json`. The full repository split and concrete production RE instantiation are NOT compiler-checked. A subsequent isolated check compiled seven missing Mathlib dependencies and successfully checked the complete generic search-to-RE adapter; see GenericREAdapter.check.log and generic_re_build_manifest.json. This checks the search proof with the function and semantic equivalence as parameters, not production import integration. Treat the patch as a reviewable integration proposal.

### Novelty screen

The independent novelty audit retained this mechanism narrowly. Nearest prior:
- packet i automates the extensional primitive-recursiveness composition proofs
  in Computability lines 92–166 with fun_prop; it explicitly says to leave recursive
  program construction and realization proofs explicit.
- packet e section 14 shares DirectGraphEnumerator and NativeGraphEnumerator
  frontends, with distinct realizers/costs.
- packet r shares numeric and program rule schedules.

None of those deletes the independent extensional proof chain by deriving its
endpoint from the already explicit scalar realizer. All are assumed applied.
This is scoped novelty within the requested corpus, not novel recursion theory.

## Rejected ancillary idea

I investigated factoring every halted run through `t ↦ min t T` and transporting
finite-prefix properties through that equation. No direct prior narrative was
found, but the current tree has only a few small callers (`halted_trace_box`,
`runTile_after_halt`, and the finish-row allowedness branch). The helper's cost
would likely exceed the removed case analysis, while several nearby first-exit
and halting persistence directions are already prior. This should NOT be counted
as a new recommended item merely to increase the number of ideas.
