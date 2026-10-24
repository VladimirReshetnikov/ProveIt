# Independent review of the integer row certificate

Root read the complete unbounded proof and the independent checker,
which imports no builder, closure algorithm or arithmetic semantics.
At an arbitrary integer zero each actual residual vanishes. A selected
row with output coefficient c!=0 gives `|c|x=P` after multiplying by
its sign. The checker derives P directly from that row, excludes x
from its right side, checks every coefficient nonnegative and requires
every odd-power coordinate to have been certified at an earlier step.
Even powers need no sign premise. Thus each certified x is nonnegative.
Nonmonic rows are treated by a positive coefficient, rather
than an unjustified integral division; sixteen steps have coefficient4.

The seed guards are exactly `x=a²+b²+c(c+1)` on fresh unrestricted
coordinates. They force nonnegativity and represent every natural x
by the three-square theorem. Applying the ordered2236-step certificate
to1092 seeds proves all3328 parent coordinates natural before invoking
the parent's arithmetic/calculus theorem. No macro is assumed sound to
establish its own domain. The reverse map preserves all original rows
and chooses independent three-square witnesses for the seeds.

Root replayed the complete independent checker and deterministic
generator in check mode; both passed. Every seed/step, the original
prefix, fresh auxiliary coverage, all31201 collected coefficients and
the exact quartic coefficient are checked. The bundled optimized
replays and malformed-premise/negative-coefficient controls pass too.
The result is an ordinary existence equivalence for the6604-integer
quartic, with the inherited calibration and paused Lean boundary intact.
