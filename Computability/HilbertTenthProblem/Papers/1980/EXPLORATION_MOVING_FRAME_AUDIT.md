# Independent audit of round40 and final-pattern interfaces

The full read of `EXPLORATION_MOVING_FRAME_BOOLEAN_HISTORY.md`, the
fresh source residuals, and the round40 arithmetic verifier passes with
no findings. The independent rerun reports 86 operations: 46
multiplications and 40 additions/subtractions, with 31 positive
unknowns and 21 source equations. The existing finite regression was
also rerun: 5,050 proposed histories, 16 aligned histories, and three
positive aligned histories, plus the seven fixed-input canonical runs.

This audit concerns the moving-frame finite-history relation. It makes
no claim that finite-support Rule 110 is universal or that these
equations encode Cook's periodic-tail initial configurations.

## 1. Arithmetic and proof interfaces

The sole change from round39 is the operand B -> C in

    I+W*Y=C+Q*F.

The local rule and B=4C then give the exact source recurrence

    b_0=4I, b_(j+1)=4*Rule110(b_j), b_t=4F.

No additional multiplication by four is missing from the schedule.
All preliminary six-field bounds and the retained 43-operation Pell
interface are unchanged. The stronger bound

    4Y <= 4(X+D) <= 4(B+C)=5B < (21/4)B < Q

is valid before digit decoding. Together with temporal alignment, it
makes every raw successor's last digit zero. The local identity
f(a,b,0)=b then forces every source row's last digit zero. Thus the
decoded neighbors and moving update have the claimed zero-exterior
meaning, including the final row.

The new recurrence preserves the leftmost nonzero position and advances
the rightmost position by one at each step. If k is the rightmost
position of 4I, choosing m>=k+t+2 supplies enough width for every
source and final row and the auxiliary local cell immediately to the
right of the rightmost one. The positive geometric quotient remains
2^(m(t-1)), including the value one at t=1.

The auxiliary positivity claim is exact. A rightmost run of one 1
becomes a run of at least two, and a rightmost run of two becomes at
least three at the next step: the preceding zero and the last two
ones all update to one. Therefore every nonempty finite word has a
111 block within two ordinary or moving steps. For t>=3, it occurs
in a source row and makes D,E positive. The rightmost 10 pair makes
X positive, and the following 100 triple makes Z positive. B,C,Y,F
are nonzero by the persistent front. All other positive outer and
Pell witnesses follow with the previously proved bounds and even r.

For shorter histories, positivity holds precisely when some source row
contains 111. An arbitrary initial word is not claimed to meet that
condition at t=1 or t=2.

If both endpoints are fixed, their rightmost positions determine the
unique candidate height

    t=floor(log_4 F)-floor(log_4 I).

This gives a decidable exact-endpoint relation despite unbounded possible
duration when F is allowed to vary.

## 2. A fixed low-prefix halt test is cheap but decidable

For fixed k and fixed Boolean base-four pattern p<4^k, the equation

    F=p+4^k*Tail                                      (P)

costs two operations. With a nonnegative Tail it tests the lowest k
digits exactly. Strictly positive Tail excludes the endpoint F=p and
would need a separate convention or an explicit padding argument.

However, this particular observation cannot by itself provide the
missing universal halt predicate. Write the moving update as

    b'_(i)=f(b_(i-2),b_(i-1),b_i).

The first K bits depend only on the first K bits of the previous row,
with exterior bits fixed zero. Hence this prefix evolves autonomously
in a finite state space of at most 2^K possibilities. A low-k-bit
observation of F=b_t/4 reads bits 1 through k of b_t, so K=k+1
suffices. Its eventual occurrence is decidable by iterating the prefix
map until a repeated prefix is encountered. A fixed initial I can be
arbitrarily long, but only these first k+1 bits matter to that event.

The same argument covers any fixed finite observation window in moving
coordinates: include the prefix through its rightmost position. It does
not cover a location supplied by an unbounded witness or an observation
whose position moves relative to this frame.

## 3. An arbitrary spatial occurrence has additional paid work

The direct exact decomposition for a k-digit pattern p beginning at an
existential position is

    F=Prefix+Zpos*(p+4^k*Tail),
    0<=Prefix<Zpos, Zpos a power of four.              (A)

The displayed expression costs four operations before obtaining Zpos
and proving the prefix bound. Without that bound, Prefix can absorb an
arbitrary false pattern. Without the power-of-four condition, Zpos
does not represent a digit position. If Zpos is obtained as the square
of a positive divisor of v, its position is at least inside the row,
but verifying the divisor and square costs two further operations.
Pattern fit and zero-valued Prefix/Tail still require attention.

Equation (A) is an explicit sufficient implementation, not a lower
bound on all implementations. No sound implementation within three
additional operations has been established here. In particular,
anchoring p at a fixed low position to save the position arithmetic
changes the computational observation into the decidable one above.

Cook's primary theorem uses a prescribed central pattern with periodic
infinite tails and detects a finite spatial halt pattern. Even a better
implementation of (A) would not establish the required initial-condition
interface or make arbitrary finite-support inputs a replacement for
that theorem. Those remain separate construction and proof obligations.

## 4. Additional independent finite checks

`../verification/explore_moving_frame_audit.py` independently checks the
rightmost-run assertion for every nonempty binary word of length at
most twelve, checks the moving prefix's independence from higher input
bits, and verifies the periodic-orbit decision procedure for fixed
prefix observations. These are finite corroboration of the elementary
general proofs above. They neither prove a universal initial-condition
interface nor produce a new universal operation count.
