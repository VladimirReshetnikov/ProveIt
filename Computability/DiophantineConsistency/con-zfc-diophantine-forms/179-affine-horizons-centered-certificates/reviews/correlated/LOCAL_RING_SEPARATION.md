# Independent local-ring audit of the correlated four-root step

Status: accepted as an ordinary algebraic-number lemma. This note proves neither the surrounding signed Pell reduction nor inherited compiler calibration.

## Exact hypotheses and conclusion

Let F,D,Q,G,b,c be integers with F=D=1 (mod 3), Q=0 (mod 3), and delta=Q-1. Let f,tau,t,g be algebraic numbers, with either sign of every root allowed, satisfying

    f^2=F, tau^2=D, g^2=G,
    delta t^2=Q(fb-c)^2-1.

If rho=f+3tau+9t+27g is rational, then f,tau,t,g are rational. In particular f,tau,g are integers. If additionally Q=0 or Q>1, then t is an integer. No positivity, independent-squareclass, or linearly disjoint field hypothesis is needed. The radicand of t is allowed to depend on f exactly as displayed.

## Proof of rationality

Write R=Z_(3)={a/d in Q: 3 does not divide d}. Fix a finite normal extension L/Q containing the four roots, and let S be the set of elements of L integral over R. Standard integral-dependence facts give that S is a ring and is invariant under Gal(L/Q). Moreover S intersect Q=R. For the latter fact, a reduced rational whose denominator is divisible by 3 cannot satisfy a monic equation with coefficients having denominators prime to 3: clearing those unit denominators and the rational denominator gives a contradiction modulo 3.

The roots f,tau,g are integral over R, since their squares are integers. Since delta=-1 (mod 3), its inverse belongs to R. The element [Q(fb-c)^2-1]/delta therefore belongs to S. The root t is integral over S and hence over R by transitivity. Thus all four roots and all their conjugates belong to S.

If f is irrational, its minimal polynomial over Q is X^2-F. The embedding of Q(f) sending f to -f extends to an automorphism sigma of L. Apply sigma to the rational relation and subtract. The equality gives

    2f=3(sigma(tau)-tau)+9(sigma(t)-t)+27(sigma(g)-g).

Consequently f/3 belongs to S because 2 is a unit of R. Squaring yields F/9 in S intersect Q=R, impossible since F=1 (mod 3). Hence f is rational and, because F is integral, f is integral.

Now (rho-f)/3=tau+3t+9g is rational. If tau is irrational, repeat the automorphism argument with tau in place of f. It gives tau/3 in S and D/9 in R, again impossible. Thus tau is rational and integral.

Now (rho-f-3tau)/9=t+3g is rational. The number

    E=t^2=[Q(fb-c)^2-1]/delta

is rational, belongs to R, and is 1 (mod 3), since f is an integer. If t were irrational, its conjugation in the normal closure gives t/3 in S, hence E/9 in R, again impossible. Therefore t is rational, and then g is rational. The usual denominator argument gives g integral.

This proof includes negative G, zero g, repeated roots, correlated fields, and reducible defining algebras. If G=1 (mod 4), the conclusion additionally implies G>0 and g odd. No root sign has been silently selected as positive.

## Adjacent-Pell denominator descent

If Q=0, then t^2=1. If Q>1 put u=fb-c in Z. We have

    Q u^2-(Q-1)t^2=1.

Write |t|=a/m with gcd(a,m)=1. Clearing denominators gives m^2 | Q-1. If |u|=1 then |t|=1; u=0 is impossible. For |u|>1 reflect signs to u>1,t>0. Then

    u<t<Qu/(Q-1).

The integral first coordinate and rational second coordinate

    u'=(2Q-1)u-2(Q-1)t,
    t'=(2Q-1)t-2Qu

obey the same norm equation. The inequalities give -u<u'<u, and u' cannot be zero. The denominator of t' remains exactly m, because 2Q-1=1 (mod m). Repeating after independent sign reflections decreases the positive integer |u| until |u|=1, proving m=1. This is an unbounded descent, not a finite test.

## Correlated product warning

The norm has to use triangular choices. For every signed f with f^2=F, choose each of the two roots t of delta t^2=Q(fb-c)^2-1, and independently choose tau^2=D and g^2=G. The product of the resulting 16 factors rho-f-3tau-9t-27g is valid even if some values coincide. It must NOT be replaced by an independent four-radical product using a single t radicand held fixed while f changes sign.

Equivalently, compute the determinant in the free rank-16 quotient algebra defined by these four monic triangular relations (over Q where delta is inverted). Reducibility and multiplicities do not invalidate that determinant identity. A zero product gives an actual complex root quadruple to which the preceding lemma applies.
