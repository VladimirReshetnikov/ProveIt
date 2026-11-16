# Conditional one-parameter separation closure

`simRuleSeparation_closedOnce` proves the numerical compiler axiom-leaf implication for `∀p`, given source sequent validity and membership of `∀p`, an open property `φ : IsSemiformula SourceL 1`, the explicit equation `free SourceL p = sepRoot φ`, and `SeedAdmission` for the open axiom node at `simPushFree e`. The proof generalizes the independently verified seeded open-separation leaf and applies the general universal compiler rule. Models satisfy PRA and IΣ₁; codes and formulas may be nonstandard. The single axiom report contains `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Both the existence of a suitable coded `p` and the required pushed-environment admission are explicit hypotheses and are not established by this theorem. Consequently this is not a general universally closed separation supplier, a PA interpretation, native iPRA proof, or a consistency implication.

An independent one-source suffix replay exited 0 in `/tmp/pa194-one-parameter-separation-replay.log` against the separately replayed open-separation and unrestricted-universal-rule outputs, with the latter and other workspace/foundation objects retained prebuilt. The checker pins this source and the open-separation object before and after; it does not authenticate the full transitive provenance of other overlays. From the repository root, select a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-one-parameter-separation.sh "$PWD" /dev/shm/pa194-ranked-open-separation-replay-v3 /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-one-parameter-separation-replay
```
