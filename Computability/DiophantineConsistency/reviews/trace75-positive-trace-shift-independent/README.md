# Independent review: positive squared-to-linear trace shift

**PASS.** In a strictly linearly ordered commutative ring, the theorem assumes
`c>0`, `f>0`, `r≥0`, `f=1+c*d` and `f*f*(c*T−r)−c>0`. It proves both
`f*T−d*r>0` and
`f*(c*(f*T−d*r)−r)−c = f*f*(c*T−r)−c`. It assumes no separate sign for d
or T. The order argument derives `c*T−r>0`, then uses
`c*(f*T−d*r)=f*(c*T−r)+r>0` and c>0; the equality follows by ring algebra.
This generic theorem does not construct a model-natural witness or establish
a trace75 graph, halting or iPRA result.

The accepted `research/trace75-positive-trace-shift-prototype/observations/shift-attempt02/`
terminal SHA-256 is `d1aeb6a09fd2767c39ff84d3a64a71b8b66193627a82ed074ed18f67bf1f6629`;
its regular object `/tmp/trace75-positiveshift-y7sk8val/Trace75PositiveTraceShift.olean`
has SHA-256 `f37bfe2a63967448298d15fc8aac2da4ad491489453be6bcd9d73ebda8a94c7b`.
Source, copied source, runner, exact axiom report, seven input hashes including
the four direct Mathlib imports, and resource samples were checked. Attempt01
failed in a factor-order rewrite and contains `sorryAx`; it is excluded.
Tool exit 0 is author-reported; no separate outer receipt or independent Lean
replay is claimed. Full package, transitive and dynamic ancestry remains
outside this review.

`check.py` SHA-256 `c398dd153b6fbf197d6e97046ac0542e402502ae573295af9a60a9d1ad28c209`;
`result.txt` SHA-256 `3d272cf956a6a4b0678294f74674124e7343c08f635c0bdc2de6d8a592025eac`.
