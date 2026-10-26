# HA equality decidability: independent root review

26 October2026. Root read all181 main lines,63 check lines and the complete
author receipt. The result is a genuine HA derivation of
`∀x ∀y (x=y ∨ (x=y → ⊥))`, followed by capture-safe arbitrary-term instances.
It uses the proved zero/successor decomposition and one formula induction
on x, whose body universally quantifies y. The successor branch eliminates
y's predecessor and instantiates the shifted induction hypothesis at that
predecessor. Successor injectivity and nonzero are actual HA axioms.

Root checked the helper rules' finite contexts: disjunction elimination
combines supporting axiom lists, and existential elimination retains
`L ++ K`, requires `Formula.Sentences B`, and shifts the entire open context
and conclusion. The check retaining the open assumption `var0=var4` shifts
it to `var1=var5`; it is not mistaken for a sentence. Equality transport
preserves the left term's free variables around its substitution hole.

Both leaves passed independent compilation with `-M6000 -j1
-DElab.async=false`, with an empty main log and14 reports using only
`propext`, `Quot.sound`, or no axioms. Both objects match the author exactly.
Nine cached prerequisites were reused, with58 input/source/cache/object
observations rechecked. Root verified all15 durable author bundle files.
No package or whole prerequisite closure was rebuilt. Exact execution
records are in
[ha-equality-decidable-root-replay/ROOT.json](ha-equality-decidable-root-replay/ROOT.json).

This proves decidability of arithmetic equality inside HA. It does not
introduce general excluded middle, arbitrary double-negation elimination,
or prove the final equation/consistency equivalence.
