# Independent review of the fixed85 proof-marker inventory

An independently implemented bounded masking and token scan reproduced the
reported positions: 159 qualified `Classical.choice` hits in 51 selected local
modules, no hits for the inventory's listed code markers, and excluded counts
of 94 `axiom`, two `admit`, one `opaque`, and one `partial` in comments. The
two excluded `admit` instances were spot-checked as prose in
`FreeJOrdinaryTailWitness` and `IPRAOpenAtomDecision`. The review also checks
individual `Classical.choice` positions, including the two occurrences on
one line in `IPRAAddOneDirect`.

The scanner's stated limitations are material. In particular:

* It recognizes the exact qualified spelling `Classical.choice`, not every
  route to a choice-dependent term. An independent lexical scan also finds
  12 `Classical.choose` occurrences in the selected local sources, excluding
  `choose!`; those occurrences are outside the original inventory's stated
  marker set. For example, `ArithmeticAdaptiveFactorUnits2011` uses it in a
  natural-residue definition. This does not by itself determine the final
  theorem's axioms or establish a proof escape.
* An unqualified `choice` after an `open Classical` is another spelling not
  recognized by the qualified-marker check. The review includes a synthetic
  alias control, not a claim that Lean elaborates that fixture.
* A quoted identifier such as `«sorry»` can be a lexical hit without being a
  `sorry` tactic. Macro quotations, aliases, tactic execution, raw or
  interpolated-string semantics and indirect assumptions likewise require a
  Lean-aware analysis. The independent masker intentionally covers only the
  documented subset of lexical forms.

The two independent implementations agreeing on this snapshot is useful for
checking the inventory and exclusions, but is not an axiom audit. It does
not resolve the external frontier, authenticate selected source/object
providers, follow theorem dependencies, execute Lean, or establish that any
proposed iPRA endpoint or PDF equation is correct. Classical or noncomputable
uses are not automatically escapes; their actual transitive effect requires
an elaborated declaration and axiom inspection.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-fixed85-proof-marker-inventory-independent/check.py
```

The checker reads the pinned local selection, independently masks comments and
strings, compares every reported marker position and exclusion count, and runs
the described synthetic controls. It does not run Lean or mutate evidence.
