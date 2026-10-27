# Actual C222 proof-code to command-word correctness

26 October 2026. Read-only proposal; no new Lean source or compiler run.
Root now owns the first `ArithmeticProofWordRowPerm222` checkpoint. The
next genuine history result should use the accepted generic sequence
construction, followed by a definable Π1 prefix induction in IΣ1. It need
not copy the fixed C254 history or use standard-Nat proof-tree induction.

I read the complete old `ArithmeticProofWordRow254`, `ArithmeticProofWord254`,
`ArithmeticProofWordContract254`, `ArithmeticProofWordCorrect254` and
`ArithmeticProofWordNonempty254` as guides, and the complete actual Row222,
History222, SequenceHistory and ValidatorProvability222 interfaces. The
accepted current Leaf/Rule/Circuit contracts and new uniform rho8 source
were checked against those interfaces. Old compiler/execution/Good proofs
are not proposed imports. Old syntax and numeric row data already used by
the separately checked Row222 remain legitimate prerequisites.

## Fixed choice and the first row checkpoint

Select `r8 : Circuit` from `exists_rho8_circuit.{0}` before selecting an
arithmetic model or any input. Its five-slot graph is fixed syntax. Its
execution contract is uniform over **Type0** IΣ1 models; this suffices for
the existing arithmetic completeness interface. Do not silently promote
that selected witness to arbitrary higher universes. Graph interpretation
as a numeric function may itself be polymorphic without implying that
stronger execution statement.

Root's row should have inputs `(tag,payload,minorWord,majorWord)` and graph
slots `(out,tag,payload,minorWord,majorWord)`. Put
`a=first payload`, `t=second payload`, `b=first t`, `c=second t`.
The unconditional numeric word row and its validity-dependent meaning are:

| Tag | Actual source conclusion or gate | Compiled word |
| --- | --- | --- |
| 0 | truth0 only when payload0 | `discardWord`, even for rejected payloads |
| 1 | MPGate a U V; result a+1 | `mpBlockWord a minorWord majorWord` |
| 2 | U≠0; result `wal a (U−1)+1` | `genBlockWord a minorWord` |
| 3 | `rho1 a t` | `leafWord 1 a t 0 0` |
| 4–7 | `rho2` through `rho5` at a,b,c | corresponding leaves2–5 with u0 |
| 8 | `rho6 a t` | **`leafWord 6 a 0 t 0`**, respecting physical AX's c slot |
| 9 | actual `growG a b c` | leaf7 a b c 0, never old primitive rho7 |
| 10 | unrestricted `rho8 a b (first c) (second c)` | selected r8 evaluated at those four inputs |
| 11 | c≠a and c≠b, helper-free bundle222 | actual `bundleWord a b c` |
| other | rejected | zero |

The exact substantial first theorem is:

```text
row_contract(tag,payload,U,V,p,q)
  (hp : U≠0 → Contract p (U−1))
  (hq : V≠0 → Contract q (V−1))
  (hr : ArithmeticRow222.rowKernel tag payload U V ≠ 0)
  : Contract (rowValue tag payload p q)
      (ArithmeticRow222.rowKernel tag payload U V − 1).
```

These are local child contracts, not an assumed global compiler. MPGate
provides the two successor witnesses and exact major implication; Rule's
minor-first `mp_contract` then retains major top0/saved `P(A,S)`, false1
halt branches and old-counter cleanup. GEN retains label0 and child
conclusion1. Tag11's two gates follow from `hr`; c0 and a=b remain legal
when those actual gates hold. No source axiom's semantic truth is needed.
Tag10 must use r8, not direct physical leaf8 with a fabricated u≤a guard.

Root may add the small fixed GEN and bundle circuit embeddings locally;
the numeric functions and their execution contracts already exist. A
finite disjunction gives a literal Σ1 row graph; total uniqueness supplies
its Δ1 graph. No intermediate should be bounded by a possibly zero output.

## Next history checkpoint: reuse actual generic recursion

For new word history, define `positiveStep previous raw` by this word row,
using `tag=raw%12`, `payload=raw/12`, `t=second payload`, and child words
`znth previous t` for GEN, otherwise `znth previous (first t)`; the second
child is always `znth previous (second t)`. This selects **words**, not
validator values. Its Σ1 graph existentially binds the exact remainder,
quotient, projections, lookups and word row.

Use the existing `ArithmeticSequenceHistory` convention:
`step previous 0=0`, and
`step previous (raw+1)=positiveStep previous raw`.
Instantiate its fixed `stepDef` once; history starts `seqCons ∅ 0` and the
generic successor calls step at `index+1`. Do not subtract twice or confuse
the proof predecessor with the shifted command-word append convention.

The generic API already supplies actual all-internal Seq status, length
`code+1`, total uniqueness, value graphs, last-element recurrence, and
complete lookup including default0 beyond the history. Define `rawWord`
as its `value`. Actual History222's `tail_le`, `minor_le`, `major_le` prove
all three source child indices ≤raw, including raw0/payload0. Thus the
new `rawWord_succ` has precisely the same child indices as checker
`ArithmeticHistory222.value_succ`. No copied evaluator is needed.

An optional single public gate is
`compiledWord d := if ArithmeticHistory222.value d=0 then 0 else rawWord d`.
Its fixed Σ1 graph and totality are easy; the stronger assertion that zero
occurs *only* at rejected codes needs a separate nonempty-word proof and
must not be claimed from this definition alone.

## Correctness checkpoint and its actual induction strength

Use the current Leaf `Contract`, unchanged, with both arbitrary top and
saved stack. Register Δ1 interfaces for actual checker value, rawWord,
state, someState and the total stopped evaluator. Define

```text
Good d := value222 d = 0 ∨ Contract (rawWord d) (value222 d − 1)
PrefixGood n := ∀ d ≤ n, Good d.
```

Both are genuinely Π1: the state/evaluator functions are Δ1, Contract's
only extra quantifiers are universal, and the prefix quantifier is bounded.
Prove the explicit definability instances, then use
`ISigma1.pi1_succ_induction`; IΣ2 and arbitrary-predicate induction are
unnecessary. Good0 follows from actual value0. At raw+1, either the actual
checker rejects or the two exact recurrences and `row_contract` apply.
Child bounds and PrefixGood provide precisely the needed nonzero-child
contracts. Preserve their universal saved-stack quantifier for MP.

The resulting substantive endpoint is:

```text
checkDef.Evalb ![d,A] → Contract (rawWord d) A
checkDef.Evalb ![d,A] → Contract (compiledWord d) A.
```

This covers every internal proof code in every Type0 IΣ1 model, not just
standard quoted trees. The graph means actual `value222 d=A+1`; the
subtraction is discharged from that equality. It yields the same contract
from `ValidatorProvability222.CProv A` after extracting its numeric witness.
The named CProv adapter can be deferred to avoid importing its Nat adapter.

For A=false1, append the accepted `terminatorWord` and apply
`false_target_halts`, obtaining an actual stopped evaluation0 from all
tops/stacks. This is a conditional refutation compiler, not a false axiom.
Later initial-state/word-to-machine-run and nonzero-program interfaces must
be composed separately. No source PA theorem, C222 seed-validity theorem,
internal source-ZFC calibration, or HA equivalence follows merely from
the represented compiler contract.

## Authenticated cache delta and remaining boundaries

[Exact first-row cache union](c222-proof-word-row-cache-plan-20261026.json)
SHA `57020638e1b7d37373a0ed00cc3e107c49558e90be9f6e7607eb17db4d741ea8`:
132 cached modules /95 Foundation /417 artifacts /38 external boundaries,
with 1,298 repeated observations verified. It selects independent rho8
primary `ed2baf3f73a4823870ee89378a083f79758cfebfba5ffb95f0233be2f52e707f`
and accepted Row222 primary
`8eed6e75b5bdd4cb8641b33aa9e4509d9f99bf7a842d7c2ca25ab3b2a07b2aae`.
Relative to rho8's127-module closure, the five additions are Row222,
Row254, Code222Proof, Code254History and Code254Proof. Their current sources
and objects match accepted records; all shared source pins agree.

[History proposal pins](c222-proof-word-history-proposal-pins-20261026.json)
SHA `e644a388a1f7dc326a417368eaa3d24ae9c30d320a55bb98bf6bf52d2c8eba48`
adds only accepted ArithmeticHistory222 and ArithmeticSequenceHistory:
134 existing modules /95 Foundation /419 artifacts /38 boundaries before
including root's new row leaf. Both plans retain source/provider records,
all headers, companions, explicit boundary pins and topological order.
No Foundation build is needed. A preliminary metadata-only probe stopped
on an external-record schema mismatch before writing files or invoking
Lean; the frozen audit handles the actual primary-record schema.

The remaining proof obligations are concrete: root's finite represented
row/row_contract, the new generic-history instantiation, and Π1 successor
correctness. None is replaced by old254 correctness or an assumed desired
compiler invariant. These checkpoints remain separate from source-calculus
calibration and the final HA proof target.
