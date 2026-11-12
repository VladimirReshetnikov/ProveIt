# Eta-natural prototype: unit factors and signed norms

This packet contains a **source-only, unelaborated proposal** for the exact
eta-natural structural prototype in `../ordinary13-eta-zero-graph-adapter-audit/`.
The generated literal has 13 model-natural inputs, arbitrary integer port
expressions, and permits `eta=0`. No beta positivity, fixed-port calibration,
natural root, zero map, graph equivalence or iPRA endpoint is assumed or
claimed. The `.lean.src` files are inert; no Lean build has been run.

`EtaNaturalUnitGraph.lean.src` is generated from the pinned prototype JSON,
with the exact ordered rows and named fields for all four factors, output,
roots, scales, and residuals. `EtaNaturalUnitBridge.lean.src` proposes:

* a first-factor negative-unit exclusion for the **actual** shorter scale
  `b`, using `Y=(1+b)³*s` and `ell=X*Y²*k`;
* application of the pinned generic `FreeJ13.main_ne`, `aux_ne`, and
  `strong_ne` to their exact prototype factor expressions;
* signed-pair product magnitudes and those exclusions to force all four
  factors to `+1` when the prototype output is zero;
* conversion by the pinned generic `FreeJ13.unit_iff_one` to the exact
  signed residual equations, followed by their first, main, strong and
  auxiliary norm forms in the model difference ring.

The existing `FreeJ13.first_ne` does **not** match this first factor: it uses
`q³*b` as the squared scale. The proposed replacement proves its finite
`ZMod 4` exclusion separately, with no positivity hypothesis. Its 1,024
residue combinations are also independently enumerated by `check.py`.
`FreeJ13.factor_units` itself belongs to another literal graph and is not
applied here. The generic paired-product result `product5_magnitudes` is
used with the four prototype factors in their actual order and a fifth unit
factor; the three reusable negative-unit lemmas retain their complete
expression-pattern hypotheses. The bridge uses no `units_of_residues`
shortcut that would confuse exclusion of the negative signed pair with an
unproved converse about its residue.

The four *proposed* ring equations, with literal generated field values, are

```
Z² = b²*(1+ell*(ell+k))
Dstar² = U²*(1+Delta*c²)
I² = Delta*(f²−1)
y²−Delta*(f²−1)*(y²−V²) = 1.
```

They are signed-ring equations. Converting the first and main roots and
scales to model naturals, representing their magnitude, proving the
q/port/rank identities and positivity, and connecting the exact graph zero to
the eta-zero index/parity premises remain separate. The downstream
`../ordinary13-eta-natural-unit-norm-adapter-draft/` is a distinct source
proposal with its own explicit factor/representation hypotheses; this packet
does not assert the two drafts have been composed. Every expression-pattern
`rfl`, model residue proof, signed-pair reduction, `decide`, `simp`, and
`linear_combination` still needs Lean elaboration and a checked provider
closure. In particular, the generic sources' current object/axiom provenance
is not authenticated here.

From this directory, run

```
python3 -I -S -B generate.py > /tmp/eta-unit-literal.json
cmp literal-result.json /tmp/eta-unit-literal.json
python3 -I -S -B check.py > /tmp/eta-unit-bridge.json
cmp result.json /tmp/eta-unit-bridge.json
```

`generate.py --write` regenerates the literal. The second check pins the
prototype and generic sources, verifies all 1,024 first-factor residues and
200 signed finite graph evaluations, and records the draft bytes. These are
finite/source controls, not Lean proof or an all-model graph theorem.
