# Independent conditional parent-growth audit

The read-only [audit](audit.py) of `f448bc311b` exited 0 in session 95137;
its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
bind the result. Both compiled source/object hashes, recorded compiler and
direct-import exits and author wrapper session 55261 exit 0 were checked.
The 70-source comparator was rerun and exited 0; this suffix directly imports
two package modules rather than a project module. Both outputs match and the
two axiom reports on each side contain only Lean metatheory `propext`,
`Classical.choice`, and `Quot.sound`, with no warning, error or `sorryAx`.
No Lean compilation was rerun here. The parent Foundation wrapper's
unobserved outer exit and package-transitive/dynamic provenance remain
inherited. One hundred small standard examples are sanity checks only.

In an IΣ₁ model the first lemma assumes 3u+2≤count≤R and concludes 2u≤R.
The second additionally assumes q=2^u and wq=2^R and concludes q≤w, using
positivity and monotonicity of the model exponential. The statement does
not itself identify count with population, derive either inequality or the
exponential equations from an actual positive zero, establish rank phase,
bind the literal graph, or prove object-theory iPRA equivalence.
