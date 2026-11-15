# Ordinal-induction statement syntax components

This staged replay builds and audits the numeric outer constructors for the induction base, step, conclusion, and complete base→step→conclusion statement. All have fixed parameter-free Σ₁ graphs, preserve the stated source arities for internal codes, and have exact typed quotation lemmas. The step's two property placements are still separate inputs at this layer; `/dev/shm/pa194-ordinal-induction-code-audit/` adds their construction from one property.

Run from the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-statement.sh "$PWD" \
  /dev/shm/pa194-typed-schema-replay /dev/shm/pa194-ordinal-statement-replay
```

Eight source modules and a twelve-declaration axiom audit are compiled in one output. The checker pins sources and selected prerequisites; other staged overlays and Foundation are prebuilt. The successful log is `/tmp/pa194-ordinal-statement-replay.log`. These are syntax results, not an internal induction proof or a PA interpretation.
