# Internal ordinal-induction statement code

`ordinalStatementFromProperty` builds the complete ordinal-induction statement from one arity-one property code p and five supplied domain, zero and successor template codes. Its fixed parameter-free Σ₁ graph is total and unique in every PRA plus IΣ₁ model, including for nonstandard p. Given the displayed scoped template and property hypotheses, its output is a valid arity-zero source formula. The step's predecessor occurrence is generated with `substs1 SourceL (^#1) p`; its successor occurrence uses p as a cast to the larger binder context.

`ordinalStatementFromProperty_quote` proves exact equality with the quote of the repository's typed `Ordinal.inductionStatement p` when the templates and p are typed quotes. The proof also checks the two property placements. This is a syntax graph, not a proof transformer: the five templates remain parameters, and the internal source derivation of induction, the arithmetic interpretation and native iPRA calibration remain open.

Replay from the repository root with a fresh final output path:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-induction-code.sh "$PWD" \
  /dev/shm/pa194-ordinal-statement-replay \
  /dev/shm/pa194-typed-schema-replay \
  /dev/shm/pa194-ordinal-induction-code-replay
```

Three source modules and an eight-declaration axiom audit are compiled in a fresh output. Source hashes and two selected imported objects are pinned; all other staged overlays and Foundation are prebuilt. The checker rejects `sorryAx`. Successful log: `/tmp/pa194-ordinal-induction-code-replay.log`.
