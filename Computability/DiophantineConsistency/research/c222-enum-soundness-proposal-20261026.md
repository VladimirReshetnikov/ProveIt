# Actual C222 enumeration soundness: read-only scope and cache

26 October 2026. Root owns the next ArithmeticEnumSoundnessPerm222 source
and checks. This note records the exact current interfaces after complete
reading of actual EnumStepPerm222, EnumRunPerm222, FetchPerm222,
ProofWordEnumPerm222, StackCertificate222 and PreservationPerm222. The old
EnumeratorSoundness254 was read as an induction-layout guide only.
No old scheduler semantics is selected or needed.

Use only direct imports PreservationPerm222 and ProofWordEnumPerm222.
The latter already imports actual EnumRun/Fair and the forward compiler.
Define `working config := second (second (config−1))`. This is the exact
work field of the live scalar `liveValue pl np work = P(pl,P(np,work))+1`.
The formula graph can be obtained from the existing subtraction and Cantor
projection graphs; no represented history or recursion is added.

For arbitrary internal IΣ1 models, use the genuine Σ1 invariant

```
SoundConfig config :=
  (config = 0 ∧ ∃ proof, History222.value proof = 2) ∨
  (config ≠ 0 ∧ CertifiedWorking (working config)).
```

CertifiedWorking is already Σ1 with a bounded Δ1 stack certificate. Value
and the projections are represented. Thus the predicate for induction is
Σ1; it does not quantify an unbounded sequence of proof witnesses or use
induction for an arbitrary Lean predicate. Needed finite steps are:

1. `working (liveValue pl np w) = w` and `liveValue pl np w ≠ 0`.
2. `sound_exec raw np w`: if the actual command result is zero, use
   Preservation.certified_halt; otherwise use certified_step and the
   actual live state with work `stepValue raw w−1`.
3. `sound_step`: at already halted scalar0 retain its existing proof;
   at nonzero scalar unfold actual enumValue and apply sound_exec to the
   fetched raw/next pair. Actual enumValue has only this outer zero test.
   The old254 proof's additional pointer split is unnecessary because
   current fetchValue already represents both cases independently of work.
4. Σ1 induction on actual internal time using run_zero/run_succ. A final
   zero run yields the retained actual value2 witness.

Reverse soundness can remain universe-polymorphic and permits any active
pointer/candidate with CertifiedWorking work. In particular certified_zero
gives reverse soundness from `liveValue pl np 0`. The combined endpoint
uses Type0, matching the accepted forward compiler's fixed rho8 circuit:

```
(∃ proof, History222.checkDef.val.Evalb ![proof,1]) ↔
  ∃ time, EnumRun.run time (liveValue 0 4 0) = 0.
```

The left side is exactly value=2, never value=1. The forward direction is
the accepted enum_halts_of_refutation, specialized to work0; the reverse
direction uses the actual certified-zero theorem. If useful, the same
proof gives equivalence with halting from every initial work at pointer0,
candidate4: one direction uses the actual universal reset, and the reverse
specializes that universal premise to work0. Reverse soundness alone does
not apply to arbitrary uncertified dirty work.

Zero is the genuine absorbing full scheduler halt. Neither an exhausted
pointer0 nor working code0 is halt: `liveValue 0 4 0` is a positive live
scalar. In particular one must not prove SoundConfig0 from certified_zero;
SoundConfig0 requires an actual falsity witness. A dirty cached1 can cause
NIP to halt without an available certificate, which is why the reverse
theorem retains its certification premise until the explicit zero-work
specialization. Fetch of an exhausted pointer selects the next candidate
without changing the work certificate; its candidate index need not be
positive for the reverse invariant.

A literal closed ArithmeticSentence can express the displayed equivalence
using only current checkDef, liveDef and runDef. Its right side should
existentially bind the initial scalar through liveDef(initial,0,4,0), then
the internal time through runDef(0,time,initial). Type0 model validity and
complete.{0} give genuine IΣ1 theoremhood; weakening gives PA theoremhood.
This is an actual C222 checker/enumerator calibration, not source-ZFC
interpretation, binary-machine calibration or the final HA equivalence.

The [frozen cache union](c222-enum-soundness-cache-plan-20261026.json) has
SHA `a05011cfec564ec9a2647ddbbefe87a34c56d4bb5324037d8e27530acd0bf210`:
145 custom modules, 95 Foundation modules, 430 artifacts and 38 explicit
external names. All reachable import headers and a cycle-free topological
order were checked. The complete inherited and selected inventory has
12,620 repeated hash observations and 1,023 distinct path/digest pairs;
overlapping source/object records agree exactly. No new Foundation module
or unchanged prerequisite build is required.

Preservation selects its frozen author primary
`/tmp/command-preservationperm222-controller-author-bm_w113l/lib/DiophantineConsistency/ArithmeticCommandPreservationPerm222.olean`,
SHA `c59af1aeca3ac8b8453ab7255fede4a1c94099e08c3a47187ba2fd90578a6e38`.
Its independent root acceptance was pending when this plan was prepared
and is explicitly recorded as pending. Root may separately pin a later
accepted byte-identical provider without changing this historical record.
The forward Enum primary is the independently replayed
`/tmp/proof-word-enumperm222-controller-peer-ljt7x81k/lib/DiophantineConsistency/ArithmeticProofWordEnumPerm222.olean`,
SHA `03d818ae589528ef0d20aa5efb762dc4dc0eeaac7f95a0436c8f1e51d4461b72`.
Root has separately accepted the Stack checkpoint in commit0fa500a8b4.

This task only reauthenticated files and wrote the new metadata/note.
No Lean invocation, source implementation, cache population, shared-object
mutation, Foundation build or Git operation occurred. Any root replay uses
only two fresh private leaves with Lean4.32, -M6000 -j1 -DElab.async=false
and the 512MiB reserve checked before each invocation.
