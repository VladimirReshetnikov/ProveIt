# Independent shared-offset certificate audit

## Scope and provisional mathematical verdict

The construction is sound, complete, and entire-fiber unique over natural
witnesses for deterministic primitive two-counter sources whose halt has no
outgoing edge. The proof below audits the final **post-shift zero-test** variant.
Executable, schema, cost-ledger and snapshot findings are recorded separately.
No claim about arbitrary Boolean guards, arbitrary source branching, or
all configurations of the compiled cellular automaton is made.

Primitive rows are: unconditional increment; guarded positive decrement on
the updated counter; unconditional identity; zero test with zero update; or
positive test with zero update. A zero-update test's tested counter comes
from its guard, not necessarily its branch side. Source controls have distinct
integer labels. Source determinism is on all natural counter pairs.

## Construction

At each t in 0,...,H-1, use natural selectors e[t,r], two natural offsets
b[t,k], and two natural shifted postcounters z[t+1,k]. For k in {0,1}, let
P_k be zero-update positive tests of counter k and set

    b[t,k] = sum_(r in P_k) e[t,r].

Define actual c[0,k] to be the given natural input, and for t>0 define
c[t,k]=z[t,k]+b[t-1,k]. The squared residuals impose:

1. sum_r e[t,r] = 1
2. the selected source control is initial control (t=0) or the preceding
   selected target control (t>0)
3. both offset equalities above
4. both updates c[t+1,k]-c[t,k]-sum_r delta[r,k] e[t,r]=0
5. e[t,r] z[t+1,k]=0 for each zero-test row r testing k
6. the last selected target is halt (or initial=halt when H=0)

All displayed residuals are linear except the bilinear zero-test rows.
Their squares therefore have total degree at most four.

## Soundness

A sum of squares is zero over the reals precisely when every residual is
zero. Natural selectors with sum one are onehot. For the selected row:

- A zero test forces current offsets both zero, since it is not a positive
  zero-update test. Its update is zero, hence z[t+1,k]=c[t,k]. Its guard
  equation thus forces the tested old counter to zero.
- A positive zero-update test of k forces b[t,k]=1 and the other offset to
  zero. Therefore c[t,k]=c[t+1,k]=z[t+1,k]+1>=1.
- A decrement has both current offsets zero and lowers exactly its guarded
  counter. Thus c[t,k]=z[t+1,k]+1>=1.
- Increments and identities have their stipulated unconditional semantics.

Control residuals are exact under onehotness because control labels are
injective. Counter residuals impose exact updates. Induction produces an
actual H-step source computation ending at halt. A blocked control cannot
continue, and halt cannot be padded because there is no outgoing halt row.

## Completeness and uniqueness

For any H-step halting run, choose the executed selectors, then the offsets
are forced. On a positive zero-update test the tested counter is at least
one, so subtraction of its forced unit offset leaves a natural shifted
postcounter. All other offsets are zero. This gives a valid witness.

Conversely the selected edge is forced inductively by the fixed input and
source determinism. Every offset is its prescribed selector sum, and every
shifted counter is the actual postcounter minus that offset. Thus *every*
existential witness coordinate, including all selectors, offsets and
shifted counters, is unique. At H=0 there are no per-step witnesses; the
single terminal constant square vanishes exactly when initial=halt.

## Nonnegative-real extension

For nonnegative-real witnesses, add for every t the square of
sum_r e[t,r]^2-1. The selector-sum equation implies 0<=e<=1. Subtracting the
norm equation gives sum_r e(1-e)=0, whose nonnegative summands force every
selector to 0 or 1. The preceding induction then forces offsets and shifted
counters to integers. No separate integrality variables are required.
This is a *paid* extension: H extra squared residuals. It does not extend to
unrestricted signed real witnesses.

## Clock and period layer

For the pinned compiler source, zero-update rows cost one microedge. A
moving row with updated old counter c and delta d costs
3+2(Z_clock+c)+d-4S. Retaining one natural clock witness Theta and squaring
Theta minus the selected sum imposes the exact forward CA microedge count.
This residual is at most quadratic; squaring is at most quartic. The clock
witness is unique. It is not a source-step or primary-TM-step count.

On the independently justified clean-input family ONLY, the cited signed
reflection theorem gives least return period 2Theta+2 if the source halts,
and no positive return otherwise. Retaining Theta, the additional equation

    t-(u+1)(2Theta+2)=0,   u natural,

is a quartic squared residual and has at most one multiplier witness u for
fixed t and Theta. It certifies exactly the positive multiples of the least
period. The least-period residual is t-2Theta-2. These are theorem-based
period certificates; they do not replace the clean-input nonblocking and
nonrepetition arguments, and they do not apply to arbitrary malformed
source encodings or arbitrary CA configurations. Crucially, u must remain
a NATURAL witness, even if the core is given a paid nonnegative-real
interpretation. Allowing arbitrary real u>=0 would accept t=Pi+1 with
u=1/Pi for Pi=2Theta+2. This is therefore a natural-only or mixed-domain
period-multiplier theorem. The least-period row has no such extra domain
issue, since no multiplier is introduced.

## Literal source recount

Pinned source SHA-256:
38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a

Rows B=141561; zero guards Z=23429; positive zero-update guards P=52036;
moving rows M=66066; unconditional identities I=30. The per-counter counts
are Z=(14451,8978), P=(43058,8978), M=(51320,14746).

Thus the core has 141565H existential variables and 23435H+1 squares.
Retaining an exact clock adds one variable and one square. The
nonnegative-real selector norm adds H squares. Period multiplier adds one
variable and one square; least-period row adds one square only.

## Cost conventions

For H>=1, written residual term slots before squaring are exactly
566225H, counting zero coefficients as written terms. This counts an
explicit residual presentation, not a fully expanded sum of squares. The
exact-clock residual has 273693H-66065 written slots, including its separate
first-layer kappa and initial-counter terms that share monomials. The
implementation specializes natural initial counters, labels controls from
zero, and separately reports the smaller exact collected row support.

Before removing zero coefficients or collecting within rows, expanding
each square using unordered products produces at most
52492435890H-20039299671 product slots; using ordered multiplication gives
104984305555H-40078599342. At H=1 these are 32453136219 and 64905706213,
respectively. Neither is a count of globally collected distinct monomials.
The real norm adds 141562H raw slots and 10019970703H unordered product
slots. An implementation must not confuse compact residual evaluation
with cheap dense/full polynomial expansion.

The older reconstructed-old zero guard e*(z_old+b_prev) would use two
terms, but substituting b_prev by its full positive-selector sum would
introduce 702835642 extra guard slots per noninitial slice. The final
post-shift guard needs only one monomial per zero-test row per slice.
