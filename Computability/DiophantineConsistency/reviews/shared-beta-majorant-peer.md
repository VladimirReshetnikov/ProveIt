# Independent ordinary review: literal beta majorant

**Accepted.** This reviews `candidates/shared-crt-beta-majorant`, leaving
its frozen source and quartics unchanged. Lean remains paused.

The general prime-supported CRT proof only needs `H>=N,E(N,z,u),F(N,z,u)`.
For the literal unchanged source split, the beta remainder row has
positive part `D^2+(S+r+1)^2`, where `D=1+(t+1)y`. Thus its contribution
to the whole positive part establishes `E>=D^2` by addition of natural
quantities. This exact uncancelled source split matters: an arbitrary
equivalent signed polynomial decomposition would not license the same
path without a fresh check.

The frozen candidate's exact path audit succeeds. It identifies four
addition steps from `E` to the literal multiplication `D*D`, and confirms
that the bound cone contains only `t0,m0,x,y,M0,U`. It contains no encoded
index, encoded column or arithmetic-macro output. Hence `H=E+F>=1`
holds before interpreting the positive factorial/power graphs.

The stronger `H>=t` correctly uses the separately retained endpoint
`y=M0+r0+2`. Over naturals, it gives `y>=2`, then
`D>=2t+3` and `H>=D^2>=t`. The endpoint uses only addition gates, so
this order of reasoning does not assume the later CRT interpretation.
For completeness, choose the valid outer carrier and endpoints first,
then compute the new bound and reconstruct all strengthened CRT
columns. Reusing the old columns would not be justified, and is not
claimed.

The explicit off-source negative control is appropriate: at `y=0` the
literal bound can remain independent of `t`, so arbitrary-input
`H>=t` is false. No such unconditional inequality is used. The empty
generic CRT index set is treated separately, while the actual shifted
trace length is positive. The static 55-call positive-input proof and
the prime-supported factorial argument remain applicable.

I reran the exact majorant-path audit and both normal and optimized
complete candidate checkers. All passed, including source authentication,
whole SOS expansion, arithmetic graph controls and affine restoration.
The actual affine point is **3,603 natural variables, 2,943 quadratic
rows, degree four, 15,670 terms, height 127,285,252**. The retained point
has **6,179 variables, 5,519 rows, 17,417 terms, height 1,992**.

The review accepts the ordinary transformation and its inherited named
C222/refutation calibration. It does not assert a new Lean theorem or
an internal object-ZFC derivation. These findings are independent of
the sibling fixed-power-bound change; composition requires regenerating
the complete literal equations and their receipts.
