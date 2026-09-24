# Five Boolean planes for the moving-frame history verifier

This is a proof of the 84-operation finite-history component system
in `../verification/round41_1980_causal_boolean_history.py`. It is not a universal
Diophantine certificate. It refines the complete 86-operation round40
moving-frame construction without changing its physical initial and
final rows, 4I and 4F.

## 1. Two source changes and their arithmetic cost

Retain round40 except for these two changes:

* Pack only D,X,E,Z,T, where T=B+hrow, instead of B,D,X,E,Z,T.
  Thus P=D+Q*(X+Q*(E+Q*(Z+Q*T))). Removing the lowest B field
  deletes one Horner multiplication and one addition.
* Replace the equality I+alphaI=W by I+alphaI=v. The addition
  I+alphaI was already computed; only its free equality target changes.

The independently checked count is 84=45 multiplications+39 additions,
with the same supplied variables and number of source equations. All
power registers, the polynomial mask scale, and the 43-operation Pell
kernel remain unchanged. D is deliberately the lowest packed field;
its even parity will be proved after decoding.

The noncircular proof below is what justifies omitting an independent
Boolean test of B. Neither small program size nor a smaller finite
check is being used as a substitute for that proof.

## 2. All preliminary numerical ranges survive

The equations B=4C, Aword=4B and

    Aword+B+C+alpha=Q

still imply B>=4, C>=1, Q>=22 and B<Q/4 before any power or
bit interpretation. The geometry gives v>=2, W=v^2>=4 and
0<hrow<Q/3, so 0<T=B+hrow<Q. The local equations

    B+C=X+2D,
    Aword+D=Z+2E,
    Y+E=X+D

and positivity give all the previous bounds on D,X,E,Z,Y, including
4Y<Q. Thus the new five-field word satisfies 0<P<Q^5<Q^6.

The new input bound gives I<v<W. Therefore the unchanged temporal
equation

    I+WY=C+QF

still proves F<W, with no Boolean assumption. The polynomial packing

    L=Q^8, N0=Q^6, 3lambda=L-1,
    r=(L-P)(L-1)+2lambda

has the same preliminary bounds N0^2<r<N0^3 and N0>=64.
Consequently the retained kernel proves q a power of two and the
central-binomial divisibility, and the periodic mask proves Booleanity
of precisely the five bounded fields D,X,E,Z,T.

As before, q=v*quot implies v is a power of two. The integer geometry
then gives W=4^m, Q=W^t and

    H=hrow=1+W+...+W^(t-1).

These deductions have not assumed that B is Boolean.

## 3. Width one is excluded without an additional equation

If m=1, then W=4 and H=(Q-1)/3 is the largest Boolean base-four
word strictly below Q. Since T=B+H is Boolean and T<Q, one has
T<=H, contradicting B>0. Thus m>=2 and v>=4. The new input
bound consequently gives

    I<v<=v^2/4=W/4.                                  (1)

This obtains the stronger initial-row bound needed below at no extra
arithmetic cost. I<v is a numerical bound, not a hidden bit predicate.

## 4. The subtraction lemma

Subtract H from the Boolean base-four word T to obtain the nonnegative
integer B. Let beta_i be the incoming borrow at digit i, initially zero.
The digit is determined by

    b_i=t_i-h_i-beta_i+4*beta_(i+1),

where t_i is zero or one, h_i is one exactly at row starts, and each
borrow is zero or one. At a row start, h_i=1, so the possibilities for
b_i are exactly among

    0,2,3,                                            (2)

and never one. A row-start digit zero is possible only when t_i=1
and beta_i=beta_(i+1)=0. Since H has zero digits in the rest of that
row, zero borrow then persists and all interior digits of that B row
are Boolean.

The equation B=4C gives b_0=0. Hence the first B row is Boolean.
The remaining task is to force every later row-start digit zero.

## 5. Row-by-row recovery of the omitted plane

Write b_j,c_j,y_j for the base-W rows of B,C,Y. Before any Boolean
interpretation, C=B/4 implies that row c_j consists of B row j's
digits 1,...,m-1 followed by the first digit of B row j+1; outside
the final B row that appended digit is zero.

The proved ranges and temporal equation imply

    c_0=I,
    c_(j+1)=y_j for 0<=j<t-1,
    y_(t-1)=F.                                      (3)

Suppose first that t>=2. By (1), the highest digit of c_0 is zero,
so the first digit of B row 1 is zero. For t=1 there is no such
digit, and c_0 is already the Boolean right shift of the first row.
In either case the first Aword,B,C rows are Boolean. The local
equations force the corresponding y_0 to be Boolean.

To justify the last sentence even though later B rows may still be
non-Boolean, reduce each local integer equality modulo the already
processed power of W. On the current prefix, the left side B+C or
Aword+D has digit coefficients at most two, so there are no carries.
The right side X+2D or Z+2E is a known bounded-digit word. Therefore
these equalities recover d=bc and e=abc on this prefix. The third
equation gives y=x+d-e; its coefficient values are exactly zero or
one. There is no borrowing into the next prefix. Higher rows cannot
alter any of these prefix equalities.

For induction, assume row j of B is Boolean, its first digit is zero,
and the next row's first digit is zero when it exists. Then row j of
C is Boolean, and row j of Aword is Boolean (its possible first digit
is the last bit of the previous, already processed B row). Hence y_j
is Boolean by the same prefix argument. Equation (3) makes c_(j+1)
Boolean. Its highest digit is B row j+2's first digit, if that
digit exists. It is therefore zero or one, and (2) excludes one.
The subtraction lemma now makes that entire row j+2 Boolean.

Starting from the first two starts, this proves that every row start
of B is zero and every B digit is Boolean. The last row is covered
because the right shift appends an exterior zero there. It also
proves Booleanity of Y. The complete decoded relation is therefore
the same moving-frame relation as in round40.

For completeness, 4Y<Q and (3) make every raw successor's last
digit zero. At row ends the right-neighbor digit is zero, and
f(a,b,0)=b, so every source row's last digit is zero. Thus the
decoded rows are genuine zero-exterior histories, not a cylinder.

## 6. Positive converse and parity

Take any fixed positive Boolean I and a valid moving-frame history
of length t whose accumulated local E is nonzero. The round40
positive-converse proof supplies all local planes. Choose width m
large enough that

    m>=k+t+2 and 2^m>I,

where k is the initial rightmost position of 4I. Such a width always
exists and does not change I, F, or the infinite moving-frame run.
Then v=2^m makes alphaI=v-I positive. All other canonical outer
bounds and positive witnesses remain exactly as in round40.

The fields D,X,E,Z,T are Boolean and below Q, so their new P is
Boolean. B's unit bit is zero; consequently the local product D=bc
has unit bit zero. Since D is the lowest field, P is even. The
polynomial packing gives even r and the same central-binomial
divisibility. Its original positive Pell necessity construction
therefore supplies all 17 kernel variables.

For every nonzero finite I, the rightmost run develops 111 within
two steps, as proved in the moving-frame note. Thus the converse
applies automatically to every duration t>=3, with F allowed to vary.
For fixed endpoints the unique-height/decidability boundary remains
unchanged. No raw universal input or periodic-background halt
interface has been supplied by this reduction.

## 7. Independent finite checks

`../verification/explore_five_plane_moving_frame.py` enumerates Boolean
T=B+H, without assuming B is Boolean. It derives the unique Boolean
D,X from B+C and E,Z from Aword+D, then tests the numerical bounds,
positivity, temporal equation and input bound. It checks that every
admitted word has the proved Boolean B and zero row starts. It also
tests canonical positive moving histories and the stronger input
bound after widening their rows. Finite checks corroborate the
general subtraction and induction proofs; they are not a universality
claim or a replacement for the full arithmetic residual checker.
