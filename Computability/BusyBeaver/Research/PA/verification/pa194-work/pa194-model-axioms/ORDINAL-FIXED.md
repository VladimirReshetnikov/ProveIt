# Ordinal-induction code with fixed typed templates

In every model of PRA plus IΣ₁, `ordinalInductionCode p` specializes the previously audited six-input numeric ordinal-induction constructor to the five actual typed domain, zero and successor template quotes. `ordinalInductionCode_definable` gives model-local Σ₁ function definability in p; its proof uses those five model values as parameters. `ordinalInductionCode_scoped` proves an arity-zero result for every internal arity-one p, including nonstandard codes. `ordinalInductionCode_quote` proves exact agreement with the quote of the existing typed `Ordinal.inductionStatement p` for each standard typed property p.

The definability theorem is model-local with parameters; it does not yet supply one parameter-free arithmetic graph uniform across models. No internal source proof-code transformer or PA interpretation is proved here.

Run from the repository root with a fresh final output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-ordinal-fixed.sh "$PWD" \
  /dev/shm/pa194-ordinal-induction-code-replay \
  /dev/shm/pa194-ordinal-statement-replay \
  /dev/shm/pa194-ordinal-fixed-replay
```

The source is rebuilt against staged prebuilt dependencies, the source and one key imported object are pinned, four axiom reports are checked, and the checker rejects `sorryAx`. Successful log: `/tmp/pa194-ordinal-fixed-replay.log`.
