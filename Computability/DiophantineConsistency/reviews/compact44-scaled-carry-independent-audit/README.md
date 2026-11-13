# Independent scaled digit and local carry audit

The read-only [audit](audit.py) of `ef9fa9c4f5` actually exited 0 in session
41531; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/object/log chains, complete window-provider
overlays, direct imports, recorded child and outer exits, and a successful
independent parent-audit rerun. Each side reports all six expected theorems
with Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`, without
warnings or `sorryAx`. No Lean compilation was rerun.

The remainder bound is proved by Σ₁ induction for arbitrary model digit
bound D under its explicit per-digit hypotheses. Two finite-family bounds,
the scaled repunit mass inequality under its explicit mass hypothesis, and
the two local zero-carry/column identities are also checked. The index types
for the weighted sums are external finite types. The results do not construct
a global end-around carry, establish actual MC digits, derive a clean
predecessor from the graph, simulate a machine, calibrate a checker, or prove
an internal PRA equivalence.

The first exploratory attempt failed and printed `sorryAx`; it is not proof
evidence. The inherited window provider lacks a complete printed axiom
inventory; Foundation outer-wrapper, package-transitive/dynamic ancestry and
sampled-resource limitations remain.
