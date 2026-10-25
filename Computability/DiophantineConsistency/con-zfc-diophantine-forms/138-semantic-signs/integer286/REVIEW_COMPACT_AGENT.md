# Independent mathematical review of the direct integer branch

Reviewer: a separate agent in the same AI-assisted research workflow,
responsible for the compact positive branch rather than the direct-integer
construction. This is an ordinary mathematical review, not an external
human endorsement or a proof-assistant certificate.

## Scope and conclusion

I read the current `PROOF.md` (319-variable parity companion),
`PROOF_ORIENTED.md` (286-variable principal), and the retained
`input/INHERITED_PROOF.md`. I also inspected the power-call/restoration
metadata and the retained `DERIVED_LABEL_RANGE_PROOF.md`, and checked
the corresponding main arguments in the combined report draft.

**Conclusion:** the new parity restrictions, abscissa orientation,
semantic sign recovery, zero-representative extension, and linear cofinal
modulus have sound ordinary proofs in the stated dependency order. I found
no new circularity or missing sign premise. This assessment inherits the
identified C222/refutation and factorial/CRT source theorems; it does not
claim that every transitive formal dependency or every expanded coefficient
was independently rebuilt by this reviewer.

## 1. Even frame and signed anchor

The even frame W=2+2 sum(atom^2) is positive independently of all unproved
front signs. The actual horizon atom t>=16 gives W>=514. The parametrization
A=2a^2-1 permits -1 and 1 algebraically, but the frame norm excludes both
because W^3(W+2)(2z+1)^2 is strictly positive. Thus A>=2 and A is odd
before Pell classification is used.

The old frame argument at W+1 then gives a positive index divisible by W,
so A>=X_W(W+1)>W^W and A-1>4W^3. No unvalidated power output is assumed
positive in this step: only its square contributes to the frame.

The replacement J=2C^2(2e+1) guarantees J!=0 and C^2 divides J, even for
negative e. In the common norm the correct classification is |J|=Y_l(A)
and |H|=X_l(A). The index-divisibility lemma is unaffected by this absolute
value. The comparison center D=1+4J(2d+1) still has |D|>=3 and D=1 modulo
4C. Replacing D by |D| in positive Pell classification only changes
independent coordinate signs; polynomial base transfer and the signed
index congruences still give i=+/-W modulo 2C. With 1<=i<=C and W<C,
the sole possible value is i=W, so C=Y_W(A).

Completeness is also compatible with both new parity choices. For even W,
A=X_W(W+1)=2X_(W/2)(W+1)^2-1. The recurrence gives
Y_W(W+1)/W odd. At odd A, v_2(Y_n(A))=v_2(n), while the binomial expansion
gives C^2|Y_(WC)(A). For l=2WC, doubling gives 2C^2|Y_l(A), and the
valuation identity shows the quotient is odd. Thus an integer e exists.
The common abscissa is odd and coprime to J, so the two comparison-center
congruences are compatible modulo H and 8J. There is no unsupported
simultaneous Pell-solvability assumption.

## 2. Orientation and negative exponents

The pooled row must be interpreted modulo A-1, not as a bound on the
actual principal abscissas. Its reduced error is

    sum_i ((epsilon_i j_i-k_i)^2+(sigma_i-1)^2).

The cap gives j_i<W and the frame gives |k_i|<W. Each term is less than
4W^2, so with fifteen pairs the total is below 60W^2<4W^3<A-1. Since it
is nonnegative and divisible by A-1, it vanishes. This forces the positive
abscissa for every pair, including the zero-index case, and fixes each
ordinate's signed index. No abscissa cap is needed.

For 1<=n<W and A>W^W, the modulus T=2An-n^2-1 exceeds W^W+W. Positive
and zero exponents are recovered by ordinary small-residue uniqueness.
For k=-h<0, the positive-abscissa norm identity gives mn^h=1 modulo T.
The exact size estimate |mn^h-1|<T gives equality over Z, impossible when
n>=2 and h>=1. This argument allows a negative or zero candidate output
m; no sign premise on m is smuggled in. Base one is used only with an
already positive horizon t and yields output one.

## 3. The q=1 and K=0 boundary cases

The initial odd square only proves q>=1, which is sufficient for the
nine actual representative exponents because their bases are q+1>=2.
It is correct not to use q>=2 at that point.

Independently, the oriented (F^2+1)^t request and the two retained ceiling
guards give V>=1, B>=1, and FB=V+s>0. Hence F>=1 and B>F>=1, so B>=2.
The linear relation y=V-1 gives y>=F+1 without assuming F=t!.

After the nine actual representatives are known nonnegative, H0>=3.
The B^K power certificate gives K>=0. If K=0, the literal endpoint implies
L=1+(t+1)y divides the nonzero number x-1, whose absolute value is
3+t+y+F. But

    L-(3+t+y+F)=t(y-1)-F-2 >= (t-1)F-2 > 0.

This excludes K=0 before using a positive exponent for the radix.
Since K is even, K>=2, and only now does the second graph give q>=36.
Thus q=1 cannot survive the complete bootstrap and no step relied on its
premature exclusion.

The q^(x+1) graph then gives x>=-1. The possibility x=-1 would require
L>2 to divide -2, so x>=0. The sign of its endpoint quotient follows
from this endpoint and L>1; the removed radix slack is nonnegative
because q=(BH0)^K>B.

## 4. Zero representatives and remaining quotient signs

The nine stored coordinates may equal -1 because their actual values are
stored+1. The proof correctly works with the actual values a_i>=0 instead
of pretending the stored coordinates are natural.

For a_i=0 every positive-order binomial coefficient is zero, which is
allowed by the prime-power range lemma and the digit rows. More generally,
the range lemma's implication p^e|binom(a,k) => a mod p^e<k includes
0<=a<k. If p^e>=k, the residue equals a in that case; if p^e<k the result
is automatic. The local calculus parameters themselves allow zero.

The retained derived label is a sum of nonnegative constructor codes and
other nonnegative terms plus one. It remains positive at zero arguments.
The explicit choice n=max(1,a_a,a_b,a_c,a_d) and H0=3+2 sum a_i ensures
n+1<=H0 even when every actual representative vanishes. The old positive
DAG coefficient bound therefore continues to apply.

Once the power meanings have been recovered, each paired remainder row
has r+s=L_i-1>=0 and rs>=0, forcing r,s>=0. Ordinary Euclidean division
rows then force the quotient signs. A nonnegative numerator is sufficient
for this implication; strict positivity should not be asserted for every
intermediate numerator when a representative is zero. This is a wording
precision, not a mathematical gap in the argument.

## 5. Linear cofinal modulus and odd-square completeness

The completeness order is noncircular: choose a finite proof tree, then a
horizon t=16+h0^2 dominating every finite decoded label and parameter,
then F=t!, V=(F^2+1)^t and y=V-1. Every pending multiset has at most t+1
members and each weight is at most (t+1)F. The inequality

    ((t+1)F)^(t+1) < F^(2t) <= (F^2+1)^t-1

follows from F>(t+1)^2 at t>=16. It supplies the same accumulator bound
that the larger old modulus supplied. Also F|y, so the original beta
moduli remain pairwise coprime.

After choosing the beta CRT code, fix R,K,B,N and choose the independent
representatives at precision 2K. Only then define H0 and q. Therefore no
CRT choice depends on a radix that itself depends circularly on the same
choice.

Every factor 1+F^2/i is odd because i|F and F is even. Thus B is odd,
H0=3+2 sum a_i is odd, and K=2R is even. The canonical integer
v=((BH0)^R-1)/2 supplies q=(2v+1)^2. The old positive representative
choices remain available in completeness; the new soundness extension
to zero representatives creates no new completeness obligation.

## 6. Combined-report inspection

The main report's statements and dependency order agree with these proofs.
One formatting typo was reported to the root author: the radix display
had `,quad` instead of `,\quad`. The review does not certify the final
rendering, complete residual appendix, or the unrelated compact branches;
those have separate exact and visual checks.
