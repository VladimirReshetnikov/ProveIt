# Candidate comparison and a checked CM215 transfer

Snapshot: `b6c7087477e51c017003bd729e712c8969733223`.

## Main recommendation

The existing conditional-marker CM215 is the easiest **additional endpoint relative to the already verified K215**. This is an incremental-proof claim, not a theorem that CM215 has the shortest possible proof from first principles. It is an existing machine, not a newly discovered 215-state table.

Its six-row binary patch admits a whole-tape positive block simulation. The source, calculus, source compiler, enumeration cutoff, and old initialization theorem can all be reused. A second derivation of 6,176 arbitrary-natural primitive cases is unnecessary for this route.

The contribution in this packet is a new compiled Lean proof of that transfer using a three-clause **one-step inductive invariant**. This strengthens and simplifies the presentation of the repository's existing ordinary proof, which argues about predecessor history. It does not invent the original marker construction or the original ordinary all-tape simulation theorem.

## Proof ingredients and status

`CM215Tables.lean` contains both literal dense transition tables, each independently matched against its pinned `.tm` bytes by `check_lean_binding.py`. Fourteen kernel-checked Boolean certificate blocks cover all 216 controls (including halt) and both symbols. Three finite facts follow: ordinary transition commutation, terminal agreement, and the incoming-edge conditions needed by the invariant. No `native_decide`, extra axiom, or unchecked external certificate is used.

`CM215Invariant.lean` uses arbitrary tapes `Int → Bool`, an integer head, and 216 controls. On the old machine, in native labels:

- control 52 implies the left cell is one;
- control 176 implies the current cell is one or the left cell is zero;
- control 156 implies the right cell is one.

The dense labels are respectively 52, 170, and 151. The third clause removes the need to reason about a two-step history when the exceptional caller 189/1 enters 156. All three clauses are vacuous at control zero, and preserved in one source step.

`CM215Transfer.lean` proves `CM215.all_tapes_halts_iff`: for every binary tape and every integer head position, the exact two tables started at control zero are equihalting. Every source transition uses one or three target transitions; the exposed local theorem gives a strictly positive block length at most three. The source and target tapes and heads agree at block boundaries, while source control 176 maps to target control 52 and other controls are fixed. Intermediate blocks never halt.

The target control 176 is a temporary marker-reader state, so the invariant is a property of the **source** run and is not asserted of every target intermediate configuration. Equivalence from arbitrary initial controls would be false without an invariant hypothesis.

Lean 4.32.0 compiled all three concrete modules and `PositiveStutter.lean`. The axiom reports for the all-tape halting theorem, nonhalting theorem, and conditional calibration adapter are exactly `[propext, Quot.sound]`.

`check_marker_certificate.py` independently checks all 1,710 invariant-admissible combinations of a working control and the three local bits. It rejects any attempted read outside the represented window, so these are complete local cases rather than finite-tape simulations. The global arbitrary-tape induction is in Lean. Four local cases use three target steps; the others use one.

The separate repository-Core bridge and any final import of `KEndpoint215` must be reported with their own actual build status; the standalone `calibration_transfer` theorem explicitly takes the old refutation equivalence as a premise. It does not silently assume a new consistency axiom.

## Comparison

The following runtime counts are measurements reported by the pinned candidate packets. They are not new reruns in this comparison. The new transfer proof avoids depending on CM215's old symbolic-runtime receipt.

| Candidate | Primitive cases | Symbolic rules | Blank prefix | Additional proof burden |
|---|---:|---:|---:|---|
| Primary K215 | 6,176 | 1,698,790 | 95,714 | Already compiled in Lean and Rocq |
| CM215 | 6,176 | 1,701,542 | 95,714 | Six-row invariant-based positive simulation; source unchanged |
| Rebalanced R41 | 6,176 | 1,640,317 | 95,714 | New address allocation and whole runtime, despite unchanged ordinal semantics |
| Direct-transfer ST215 | 6,151 | 1,617,630 | 70,506 | Changed command/compiler interface, partial AX prefix and protected stack tail |
| MP-first transfer T215 | 6,209 | 1,610,781 | 68,442 | Changed command enumeration and one-head scheduler-credit theorem |
| rho6-210 | 6,176 | 1,699,838 | 95,714 | Two-row change but a repaired axiom-selection compiler |
| Zero-spare Z215 | 6,176 | 1,698,790 | 117,004 | Different initial state/frame, two-truth protected-tail calibration |
| Reencoded primary | 6,176 | see packet | 716,307 | Changed addresses and nonzero additive-counter seed |

R41 reduces the existing symbolic-rule count by 58,473, or approximately 3.442%. Its maximum address depth is 41 instead of 47 and its address-length sum falls from 160,305 to 149,265. The per-case clocks do not all improve: 1,427 decrease, 3,827 increase, and 922 are unchanged. These static/source measurements do not establish lower total formal-proof cost.

ST215 and T215 have fewer symbolic rules, but need additional high-level compiler, scheduler, and initialized-tail proofs. A count of two changed rows in rho6-210 likewise does not make it cheaper than CM215: that change alters which register supplies an axiom parameter and is not a whole-tape binary equivalence on arbitrary inputs. The complete axiom family is preserved, requiring an appropriate source theorem.

The existing `composed` alternative retains exactly the primary source and has 1,698,790 symbolic rules, but its differing allocation lacks the short six-row transfer used here. `commands120` changes the command order and has 1,698,845 symbolic rules and a 96,284-step prefix. Neither offers an evident proof advantage over CM215 relative to the checked baseline.

## State-reduction boundary

CM215's role merger spends its recovered label on the marker selector, so it remains at 215 working states. Its already archived helper-reuse search tries all 856 changes to the merged zero branch after deleting the selector, with explicit bounds of 96 transitions, 10 visited cells and 4,096 symbolic nodes. It finds no qualifying replacement. Most exits are bound exhaustion, not universal impossibility proofs.

The already archived 214-state return-scanner deletion is not a verified consistency candidate: a concrete arbitrary-register frame at source ordinal 26 gives the wrong successor. It does not follow that every 214-state machine is impossible, nor that this experiment's blank-run equivalence is false. The new proof does not promote that table into an accepted candidate.

## Primary evidence paths

All paths are under `Computability/BusyBeaver/Research/ZFC/` at the pinned commit.

- `candidate-k215/README.md`
- `candidate-k215/alternatives/README.md`
- `candidate-k215/alternatives/conditional-marker/README.md`
- `candidate-k215/alternatives/conditional-marker/proof/marker215-proof.tex`
- `candidate-k215/alternatives/conditional-marker/research/helper-reuse/README.md`
- `candidate-k215/alternatives/conditional-marker/research/rejected-return214/README.md`
- `candidate-k215/alternatives/rebalanced/README.md`
- `candidate-k215/alternatives/direct-transfer/README.md`
- `candidate-k215/alternatives/mp-first-transfer/README.md`
- `candidate-k215/alternatives/rho6/README.md`
- `candidate-k215/alternatives/zero-spare/README.md`
- `candidate-k215/alternatives/reencoded/README.md`
- `candidate-k215/alternatives/composed/README.md`
- `candidate-k215/alternatives/commands120/README.md`
