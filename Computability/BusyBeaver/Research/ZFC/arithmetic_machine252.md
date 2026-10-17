# Representing the actual 252-state run in arithmetic

Three Lean modules now give a fixed arithmetic representation of the frozen
[252-state machine](candidate-permutation252/README.md). The action lookup and
whole-configuration step have bounded graphs in every IOpen model. Iteration
has fixed Σ1/Δ1 graphs in every IΣ1 model, including at nonstandard time indices.
On the standard natural numbers it agrees at every time with the actual blank
Core run. There are also actual IΣ1 and PA derivations of unique totality of
this represented evaluator.

The internal PA equivalence between machine halting and existence of a ZFC
refutation remains open. This checkpoint supplies its machine-side arithmetic
sentence. The separately checked [C254 history evaluator](arithmetic_history254.md)
supplies the proof-checker side; their internal translation is still needed.

## Exact table and whole-tape coding

[`ArithmeticMachineGraphPerm252.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineGraphPerm252.lean)
derives its finite action list directly from `rawTablePerm252`, without another
table copy. A generic finite compiler produces `actionLookupDef`, a fixed
parameter-free Σ0 graph. Its free arguments are output, source state and read
bit; the actual table is literal formula-construction data.

Working state q is represented by q+1, with0 reserved for halt. Each real action
has positive code `1 + 4*nextState + 2*direction + write`, where direction1
means right. Lookup0 denotes an absent source state. The unique halting action
has code4, preserving its write1 and right move. Kernel-decided finite facts
bind all504 actions to the actual typed table and bound their codes by1012.
The generic lookup selects read1 for *every* nonzero read argument; the actual
step supplies a remainder modulo2.

[`ArithmeticMachineStepPerm252.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineStepPerm252.lean)
encodes a numeric configuration as `P(state,P(left,right))`, using the literal
Cantor pairing already represented in arithmetic. The low bit of right is the
current cell; the low bit of left is its left neighbor. For write bit w:

| Move | New left | New right |
|---|---|---|
| Right | 2*left+w | right/2 |
| Left | left/2 | left%2+2*w+4*(right/2) |

The state component is the action's successor, including halt0. Halted and
invalid positive-state configurations absorb, retaining their whole tape.
The configuration pairing is bijective over Nat, so `stepValue_nat` covers
every input code, not merely reachable configurations. Its `nativeStep`
is the numeric simulator proved against the whole actual tape in the earlier
[Std-only adapter](arithmetic_machine_perm252.md).

The bounded formula `stepDef(out,input)` uses witnesses bounded by the input,
action bound1012, or final output, according to the appropriate pairing or
division lemma. Rejected/absent actions can preserve arbitrary input codes;
the proof does not bound their intermediate data by a zero action result.
The initial configuration code is1; its first step is406. The actual final
transition maps `(76,left,2*r+1)` to `(0,2*left+1,r)` before absorption.

## Internal iteration and the halting sentence

[`ArithmeticMachineRunPerm252.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineRunPerm252.lean)
uses Foundation's `PR.Blueprint 0` and `PR.Construction`. The zero graph is
`r=1`; the successor graph has arguments `(out,previous,index)` and applies
the exact `stepDef` to previous. There is no table oracle or additional model
parameter. Internal Σ1 induction supplies existence and uniqueness of the
coded iteration history at every model time.

The checked interfaces are:

```text
runDef(out,time)                 ↔ out = run(time)       [every IΣ1 model]
run(0)                          = 1
run(time+1)                     = stepValue(run(time))
run(time)                       = encodeConfig(numericRun(time)) [Nat]
first(run(time)) = 0            ↔ actual Core run(time) is halted [Nat]
```

`runDeltaDef` gives the corresponding fixed Δ1 graph. The closed Σ1 sentence
`haltingSentence` is:

```text
∃ time config, runDef(config,time) ∧ firstDef(0,config).
```

`haltingSentence_nat` proves that this sentence is true in Nat exactly when
the actual frozen table halts from blank. Its interpretation at nonstandard
indices belongs to the arithmetic model; it is not an external Core run at
a supposed nonstandard Lean Nat.

The closed arithmetic `totalitySentence` is:

```text
∀ time, ∃ config, runDef(config,time) ∧
  ∀ other, runDef(other,time) → other=config.
```

`isigma1_proves_totality` and `peano_proves_totality` are actual object-theory
derivability statements for that sentence. They follow by arithmetic
completeness from the all-model theorem, then weakening. They establish
total unique evaluation, rather than an internal consistency equivalence.

## Verification and reproduction

The [maintained verification](results/arithmetic-machine252-verification.json)
freshly checks eight arithmetic modules and eight stored audits: the five
existing checker modules followed by these three machine modules. It records
196 named axiom reports and237 callers, all using only standard Lean axioms.
The three new modules/audits emit no warnings; the Cantor prerequisite emits
five existing simplification-style warnings. The full runner's top-level
`warning_count` counts only the new checks; the compact record separates the
prerequisite and total counts.
Only the needed source- and object-matched core imports are reused from the
successful168-unit integration. These arithmetic extensions remain outside
the Std-only core runner and umbrella.

The [source review](results/arithmetic-machine252-review.json) records the
precise source/audit identities and scope. The runner also records the pinned
compiler, existing Foundation/Mathlib providers, fresh objects and post-check
identity checks. It builds no dependencies and downloads nothing. Attribution
for the original calculus, program and table is preserved by the linked
candidate and imported modules.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine252.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --core-evidence /path/to/successful-168-unit-verification.json \
  --core-cache /path/to/its/core-cache \
  --output /outside/new-empty-machine-check
```

Use an absolute `--lean` path and repeated `--library-path` arguments if the
pinned compiler or built libraries require explicit selection. The default
checks all three new modules. `--through graph` and `--through step` name
smaller scopes; `--prepare-only` checks configuration without proving anything.
