# Zero-uniqueness formula quotation and translation

`uniqZero_quote` identifies the numeric `uniq zeroT` formula with the quotation of the standard PAeq sentence `∀x∀y (x=0 → y=0 → x=y)`. `tr_uniqZero_quote` then identifies its canonical identity-packet translation with the quotation of the exact typed source translation. Both hold in arbitrary IΣ₁ arithmetic models, including nonstandard ones. They are syntax/code theorems; they do not show that the source theory proves the translated formula or discharge `NameFacts.uZero`.

Replay from the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-uzero-quote.sh "$PWD" /dev/shm/pa194-uzero-quote-repo-NEW-new
```

The two source modules are rebuilt sequentially in one output with one clean axiom report each and no `sorryAx`. Foundation and the retained baseline object overlays listed by the checker are prebuilt.
