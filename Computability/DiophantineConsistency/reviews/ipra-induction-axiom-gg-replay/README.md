# Native intuitionistic induction proves the GG induction axioms

`induction_scheme_gg_in_theory` proves that for any intuitionistic theory T
containing every `IPRANativeInduction.nativeInduction` instance and any
`σ ∈ Foundation.Arithmetic.InductionScheme language Semiformula.Open`, T
proves the Gödel–Gentzen image `σᴺ`. The proof uses native implication and
the exact Foundation x+1 step. It constructs an open finite-parameter matrix,
proves its native induction axiom belongs to the assumed scheme, identifies
its embedding with the closed free-parameter body, and applies the already
proved GG body equivalence.

This does not prove GG images of PRA equality, defining or basic axioms, nor
does it identify the translation of the ZFC consistency side or establish the
end-to-end iPRA theorem. External transitive ancestry is inherited.

Run `python3 Computability/DiophantineConsistency/reviews/ipra-induction-axiom-gg-replay/replay.py`.

Author replay PASS; the five axiom reports were parsed and contained only
`propext`, `Classical.choice`, and `Quot.sound`. The replay script rejects
warnings, errors and `sorryAx`; this stricter axiom-set comparison was done
separately on the frozen checks log.

Independent peer PASS; all four source/object/full-log rows match author,
and all five frozen axiom reports again contain only the standard Lean trio.
