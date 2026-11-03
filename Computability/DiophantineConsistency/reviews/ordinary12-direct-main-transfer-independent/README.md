# Independent review of the conditional direct-main transfer

`DirectMainTransfer.transfer` is a theorem over an arbitrary commutative
semiring. It assumes the exact balance

```
U*(X+a*c)+H*(U*G+R+1) = H*k+U*main
```

and concludes

```
H*(U*w+R+1)+U*(X+a*c+H*G) = H*k+U*(main+H*w).
```

No positivity, order, nonzero or model hypothesis appears in this theorem.
A separate independent sparse-polynomial check verifies that each conclusion
side is its corresponding assumption side plus `U*(H*w)`. This gives the
transfer by substitution, without subtracting or canceling in the semiring.
The separate `old_contribution` theorem and independent polynomial check
establish `((q*w)*(q³*s))*q=(q⁵*s)*w` for arbitrary semiring values.

The adjusted `main+H*w` is an algebraic congruence witness; neither theorem
asserts that it is the Pell root. The input balance is an explicit hypothesis,
not a conclusion obtained from a graph. Constructing the old valuation,
deriving the needed balance and other hypotheses from a modified graph, and
applying a graph congruence theorem are still open. These lemmas do not
establish a 90-operation equivalence or an internal iPRA proof.

The recorded author run exited zero with empty stderr, no warning and no
`sorryAx`. Both results report only `[propext]` as a Lean metatheory axiom.
The source, source snapshot, runner, Lean binary, logs and output object match
the receipt. The selected `DirectMainProjection` import matches the exact
object from the earlier accepted projection run. The review rehashed the
1,291-file selected 92-halt union and symlink targets before and after, and
reran the previous read-only projection/norm review.

At preflight the author recorded one existing Lean process; both captured
run samples recorded two Lean processes and at least 18,196,964 KiB available
memory. Samples are not continuous monitoring. Run `python3 -I -S -B check.py`
from this directory, or pass the script path from another directory. The
captured review exited zero with empty stderr; see `observations/stdout`. It
requires the retained absolute `/tmp` provider and output paths. No Lean
process was started during this review.

This is an independent inspection of a single author run, not a fresh
independent kernel replay. The selected-provider check does not establish
complete historical source-to-object, package-transitive or dynamic ancestry.
