# Internal Pell descent and classification

26 October 2026. Proposed new main/Checks import only the accepted
ArithmeticPellRecurrence main. The exact dependency scope is the prior
95 cached Foundation modules/380 artifacts, plus its accepted recurrence
main:96 cached modules,95 Foundation,381 artifacts,38 external names and
114 boundary companions. No dependency or Foundation refresh is allowed.

The target is actual uniform classification in every IΣ1 model: each
natural arithmetic solution x²=1+(b+1)(b+3)y² has an internal represented
recurrence index time<=y with both coordinates exactly x,y. Prove the
reverse direction too. Do not assume an external Pell classification or
an internally represented witness as an additional premise.

For y>0, prove justified natural differences
u=(b+2)x-d*y and v=(b+2)y-x, with u>0,v<y, the same norm, and both exact
inverse recurrence identities. Polynomial identities and order comparison
of squares suffice, without signed subtraction or a ring assumption.

Classify by actual Sigma1 order induction on y. To stay in the induction
class, universally quantify x only up to (b+2)y+1 and prove that polynomial
bound from the norm first. Every recurrence graph and induction invariant
must be explicitly definable; an unrestricted meta-level induction on
arbitrary arithmetic model elements is not acceptable.

Freshly compile only the new pair with pinned Lean4.32,
`-M6000 -j1 -DElab.async=false`, one thread and a512MiB reserve. Fully read
sources/drivers first and retain every failed attempt. Independently
review/replay the final pair before acceptance. Carrier congruences,
cofinal simultaneous witnesses, literal machine composition and the final
PA/HA equivalence remain separate work. The displayed equation is unchanged.
