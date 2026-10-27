# Internal Pell recurrence

26 October 2026. This plan targets the arithmetic bridge that the final
PA-to-HA transfer still needs. It does not replace that bridge by external
standard-natural Pell theorems.

Add exactly `ArithmeticPellRecurrence.lean` and its Checks, importing only
Foundation's HFS.PRF package and Mathlib.Tactic.Ring. The authenticated
selected closure has95 cached Foundation modules,380 selected artifacts,
38 explicit external names and114 boundary object companions. No existing
source refresh or Foundation build is planned. The read-only inventory
checks631 pins and every current selected import header.

Parameterize the base by b+2 and use d=(b+1)(b+3). Thus d+1=(b+2)^2 in
every arithmetic model, without truncated subtraction or a hidden sign
condition. Foundation's own represented pairing may be used as an internal
recurrence state; this state is independent of the machine's Cantor coding.
The literal recurrence is

    (x,y) starts at (1,0);
    (x,y) advances to ((b+2)x+d*y, x+(b+2)y).

Use PR.Blueprint/Construction to supply fixed Sigma1 and Delta1 graphs
and totality for every internal parameter and time in an arbitrary IΣ1
model. The desired first endpoint includes both coordinate recurrences,
the norm x²=1+d*y², x>=1, y>=time, strict growth of y, and the addition
formulas. Each internal induction must have an actual Sigma1-definability
certificate; unrestricted Lean induction on model elements is not allowed.

The norm step uses only commutative-semiring polynomial identities. It
must not assume a ring or inject natural arithmetic into an unjustified
integer model. The natural specialization can use ordinary Lean Nat
induction, but cannot substitute for the uniform model theorems.

Compile only these two new leaves privately with pinned Lean4.32,
`-M6000 -j1 -DElab.async=false`, one thread and a512MiB reserve. Retain
every failed source, driver, command, log and timing. Independently review
and replay the final source before accepting a checkpoint.

This first package will not classify all Pell solutions, prove the needed
congruences or cofinal witness bounds, connect the recurrence to every
literal carrier, or close the PA/HA equivalence. Those are subsequent
obligations. The displayed equation and its PDF remain unchanged.
