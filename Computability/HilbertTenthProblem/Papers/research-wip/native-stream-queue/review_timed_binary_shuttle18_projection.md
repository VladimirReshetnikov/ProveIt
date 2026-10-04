# Independent review of the binary timed-orbit projections

PASS, with no author correction requested. The six complete circuits in
[timed_binary_shuttle18_projection](timed_binary_shuttle18_projection.md)
represent the stated explicit binary orbit on natural external gap and time,
with integer external positions. The final circuit has 31=8M+23A paid
operations, two natural witnesses, and exact degree four. Its nonnegative-real
witness fibers coincide with its natural fibers on this external domain.
This is a decidable orbit family, not a universal polynomial or a generic
rule-to-chart compiler.

The [independent helper](review_timed_binary_shuttle18_projection.py) reads
only authenticated source text and JSON. It never imports or executes the
author helper, delivered compact module, or historical suite. Its
[receipt](review_timed_binary_shuttle18_projection.json) pins the complete
author trio and both frozen source dependencies. The full author helper and
companion were also read directly.

## Full source and coefficient checks

The checker extracts only the three assignments defining `d`, `T`, and
`residuals` from the inert compact module's AST. A restricted mathematical
expression reader interprets names, integer constants, addition, subtraction,
and multiplication; no general Python evaluation or import is used. An
independent exponent-vector polynomial engine then expands each actual saved
source, all retained residuals, and the complete finalizer.

| Complete saved source | M | A | Total | Witnesses | Output terms |
|---|---:|---:|---:|---:|---:|
| Four-witness baseline | 11 | 28 | 39 | 4 | 73 |
| Literal cycle projection | 10 | 26 | 36 | 3 | 69 |
| Shared projected clock | 10 | 25 | 35 | 3 | 69 |
| Phase projection, duplicate square retained | 9 | 24 | 33 | 2 | 94 |
| Duplicate removed | 9 | 23 | 32 | 2 | 94 |
| Unsquared integer Boolean term | 8 | 23 | 31 | 2 | 94 |

All 206 paid rows and every supplied input and witness are live. The output
is the final row in every array. All 493 saved full-output coefficient
entries and all 35 residual slots match the independent expansion, including
the repeated slot of the weighted 33-operation source. The mixed-finalizer
metadata declares exactly one unsquared term in the 31-operation source.
Every complete output has degree four: the coefficient of `n^4` in the
baseline, and of `x3^4` in each projected polynomial, is exactly one. This
also proves attainment after fixing any gap parameter.

The whole-polynomial identities, rather than only zero tests, establish:

- Substituting `n=x3-x-7-e` into the original polynomial gives the literal
  three-witness polynomial; its deleted last-position residual vanishes
  identically.
- The two three-witness schedules have identical full coefficients. Their
  clock identity cancels both quadratic phase terms without imposing
  Booleanity.
- Substituting `e=x2-x1-1` makes the second-position residual equal to the
  first, giving exactly the weighted 33-operation polynomial.
- `P33=P32+R1^2`, while `P32-P31=B^2-B` for `B=e(e-1)`.

These statements preserve the distinction between equality after coordinate
substitution and zero equivalence after changing a finalizer. No intermediate
register positivity is imposed and no unpaid comparison is introduced.

## Domain and inverse proof

At a projected zero with natural witnesses, Booleanity gives `e=0` or `1`.
The external integer positions then make restored `n` integral. Write
`h=x+n+1=j+u`. If `n<0`, then `-x-1<=n<=-1`, and the clock yields

    t <= (n+1)*(n+2*x+4)-1 < 0.

The second factor is at least `x+3`, so this contradicts natural time.
Thus the cycle inverse is natural without assuming that the external tuple
already belongs to the orbit. The inverse phase is Boolean and hence natural.
The duplicate-square deletion is valid because a copy of that same square
remains among nonnegative summands.

In the final source, `e=x2-x1-1` is integer before any equation is used.
Consequently `e(e-1)>=0`, and replacing its square by itself keeps exactly
the same zero condition. This argument applies for nonnegative-real `j,u`
as well. At such a zero, restored `e,n` are integers, and the first position
row gives `j=x1-3` in phase zero or `j=h+2-x1` in phase one. The domain row
then makes `u=h-j` integral. All six real fibers are therefore natural.
The inherited consecutive half-open charts establish the same unique timed
configuration and empty or singleton witness fibers.

Both domain boundaries are real restrictions, not optional conventions.
At `x=0,t=-1`, positions `(0,2,4,7)` and `e=1,j=u=0`, all five projected
sources vanish but restore `n=-1`. At noninteger external positions
`(1/2,3,9/2,15/2)`, with `x=0,t=1,j=0,u=1`, the final circuit has a false
zero: `B=-1/4` cancels `x0^2=1/4`, while the 32-operation SOS has value
`5/16`. This independently checked example is stronger than mere failure
of global real nonnegativity. It lies outside the declared integer-position
interface and does not contradict the theorem. The final circuit must not
be described as an unrestricted-real SOS certificate.

## Independent finite evidence and replay

The new finite checks use 1,128 chart states over five gaps and eight cycles,
with all natural times in the corresponding interval covered exactly once.
They give 6,768 complete source zero evaluations and 186 rational full-output
correction checks. Another 24,682 feasible negative-cycle phase cases agree
with the analytic bound. These are fresh checks of the explicit charts and
saved arithmetic, not new runs of the radius-six CA or proof of the generic
normal form. The original binary orbit theorem remains inherited from the
frozen source.

Fresh replays from `/` passed in normal and optimized Python. All checks use
explicit exceptions; JSON receipt comparison is recursively type-exact and
rejects duplicate keys and nonfinite values. This is a bounded source-review
CLI, not an audited general-purpose compiler API.

    python3 /ABS/review_timed_binary_shuttle18_projection.py --repo-root ABS_REPO --author-root ABS_AUTHOR_DIR --expect ABS_REVIEW_JSON
    python3 -O /ABS/review_timed_binary_shuttle18_projection.py --repo-root ABS_REPO --author-root ABS_AUTHOR_DIR --expect ABS_REVIEW_JSON

Frozen author hashes:

| File | SHA-256 |
|---|---|
| `timed_binary_shuttle18_projection.py` | `925151411f76d1f2e56ea729fed9bb5f1c1f990ff92e4920d160fe2e645b765b` |
| `timed_binary_shuttle18_projection.json` | `c441134593d9a593f2c599d810a6c7a48feddfb16ba85fce8d822008fa4a82bf` |
| `timed_binary_shuttle18_projection.md` | `5fad6c3268a1a7331387696c6b583e76a9608f0d194902c36c5dcb5977334875` |
