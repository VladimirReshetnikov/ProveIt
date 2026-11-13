# Independent arbitrary-digit-bound cyclic carry audit

The read-only [audit](audit.py) of `28fceaf304` actually exited 0 in session
61135; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/seed/object/log chains, complete window overlays,
direct imports, recorded child and outer exits, and a successful rerun of the
independent scaled-digit parent audit. Both logs report the four expected
names with Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`,
without warnings or `sorryAx`. No Lean compilation was rerun.

The model theorem constructs bounded end-around carries and the stated
cyclic column identities for an externally finite family, under **all**
explicit `CarryInput` hypotheses: positive word length and modulus, each
word below the word radix, digits bounded by model D, the remainder below the
modulus, the modular equality, and the scaled mass inequality. It permits
arbitrary D, including 3; it does not assume every digit is Boolean.

The theorem does not derive these hypotheses for the compact44 graph, bind
MC or K, establish temporal alignment or a clean predecessor, simulate the
machine, calibrate the checker, or construct an internal PRA proof. The
retained exploratory version had an unused-variable warning; the paired source
compiled without warnings. The window provider lacks a complete printed
axiom inventory; Foundation outer-wrapper and package-transitive/dynamic
ancestry qualifications remain. Resource measurements are samples.
