# Independent review of the pooled power certificates

Internal AI-assisted mathematics review, 25 October 2026. This is not external
peer review and is not a new formal-assistant build.

## Verdict and scope

The modulus-free two-row certificate is sound and complete under the inherited
canonical signed Pell-coordinate interface and the existing square frame. The two
power pools have a valid acyclic order in the Joint_Norm bootstrap. The literal
producer correctly authenticates the affine shifts of its old coordinates;
it does not identify actual semantic values from variable names alone.

The reviewed producer is `code/build_pools.py` (ported from the reviewed research producer). It uses
11 requests at n=q+1 and three requests at n=q. It retains the separate
requests at B, BH and F^2+1. The polynomial-row identities in that file agree with the proof below.
The final variant needs no frame change: its sharper squared-atom estimate is
proved below. A preliminary producer variant enlarged the frame; that change
is valid but unnecessary and is excluded from the principal comparison.

## 1. Exact identity with no modulus coordinate

Let A,n,m_i,X_i,Y_i,Z_i be integers, with Z_i=A*Y_i. Put

    H = sum_i Y_i(m_i-X_i),
    S = sum_i [(m_i-X_i+Z_i)^2-Y_i^2],
    T = 2An-n^2-1,
    r_i = m_i-X_i-(n-A)Y_i.

Then direct expansion gives

    sum_i r_i^2 = S-2nH-T*sum_i Y_i^2.

The two residuals

    K-2H-(2A-n)L = 0,
    S-nK+L = 0

are quadratic in the existing coordinates and the two new unrestricted
integer coordinates K,L. Together they imply S-2nH=T*L, and therefore

    sum_i r_i^2 = T*(L-sum_i Y_i^2).

The aggregate H is an abbreviation, not a new variable. T likewise is a
polynomial abbreviation, so the old explicit modulus variable and its
quadratic defining residual can be deleted. No division, exponentiation,
factorial or absolute-value operation occurs in the new residuals.

The optional norm reduction adds retained zero residuals
X_i^2+Y_i^2-Z_i^2-1 to S. It changes the polynomial specification while
preserving the same zero set and the same semantic identity on that set.

## 2. The existing square frame bounds the actual atoms

The inherited frame has the literal form

    W = 2 + sum(actual affine atom squared).

It includes the actual base, output and index of every retained power
request. Thus n^2,m_i^2,k_i^2<W, not merely |n|,|m_i|,|k_i|<W. The independent
`code/check_pool_frame.py` reconstructs all 37 parent squares exactly and,
after strict-horizon deletion, all 36 retained squares. It verifies by exact
coefficient equality that each of the 14 pooled power ports is covered.
The linear-beta substitution keeps a sum of squares and may duplicate the
V square; it does not weaken any power-port bound.

The original odd frame proves |A|>W^W. Also W>=258 since the fixed horizon
t>=16 is one of its square summands. These bounds are sufficient without
changing any frame coefficient or adding a frame witness.

## 3. Small ordinary errors force every power separately

Assume 1<=|n|, at most s<=15 summands, and canonical signed Pell coordinates
X_i=X_{k_i}(A), Y_i=Y_{k_i}(A). Put b=floor(sqrt(W-1)); this is a proof-only
integer, not a new coordinate or an operation in the polynomial. Every
|n|, |m_i|, |k_i| is at most b, and b>=16.

The standard Pell substitution modulo T sends A+sqrt(A^2-1) to n.
It is valid also for negative k because gcd(n,T)=1. Thus

    r_i = m_i-n^k_i modulo T

in the residue ring, interpreting negative powers through the inverse of n.
Multiplication by n^b clears every inverse, since b+k_i>=0. Therefore T
divides the nonnegative ordinary integer

    E = sum_i [m_i*n^b-n^(b+k_i)]^2.

Each absolute inner term is at most 2*b^(2b), and hence

    0<=E<=4s*b^(4b)<W^(2b+1)<=W^W.

Here 4s<=60<W, b^2<W, and 2b+1<=b^2+1<=W. Moreover

    |T| >= 2|A|-b^2-1 > |A| > W^W > E.

Consequently E=0 and every summand vanishes. For |n|>=2, an index k_i<0
would imply m_i*n^(-k_i)=1, impossible over the integers. Thus all k_i>=0
and all m_i=n^k_i. For n=1 or n=-1, each output is the corresponding unit
n^k_i, even if k_i is negative. The unit cases must be retained for the
initial q=1 bootstrap branch.

The proof does not claim the original r_i themselves are small: they may
be enormous Pell expressions. It bounds a congruent sum of ordinary errors
only after multiplying by the explicitly sufficient clearing power.

For completeness the original frame can be retained verbatim: choose
A=X_W(W+1), with ordinate Y_W(W+1)=W*(2z+1). Divisibility by W follows by
reducing the recurrence modulo W. The quotient is odd: for W odd, both
numerator and divisor are odd; for W even, W+1 is odd and
Y_{2j}=2X_jY_j with every X_j odd gives v_2(Y_W)=v_2(W). The inherited
squared-anchor and auxiliary CRT construction are consequently unchanged.

## 4. Acyclic order of the two pools

The rounded ceiling and the separate request at F^2+1 still prove b=|B|>=2,
V=(F^2+1)^t, |F|<b and V<b^2. The unpooled request at B gives x>=0 and
N=B^x. Because the self-radix multiplier H is odd, |BH|>=2; its unpooled
request gives q=(BH)^x.

First apply the three-way q pool. Its base q is nonzero already. If x=0,
then q=1 and the pool's unit case gives M=1. This contradicts B*d=M and
|B|>=2. Therefore x>=1 and |q|>=2. The same pool gives exact q^t and q^x.
The retained normalization ratio q^t|q^x then forces x>=t>=16.

Now |q+1|>=2^16-1>=2. Apply the eleven-way pool at q+1. Every proposed
representative exponent is consequently nonnegative, and every proposed
numerator is its exact power. This establishes precisely the signs used
later by the factorial and radix arguments, without assuming those signs
when interpreting the first pool. The signed factorial bootstrap and its
separate F=0 bound then proceed as in the strict-horizon proof.

## 5. Completeness and witness reconstruction

For semantic positive power data, each old individual power congruence holds,
so every r_i is divisible by T. Hence

    L = sum_i Y_i^2 + sum_i r_i^2/T

is an integer; put K=2H+(2A-n)L. These choices fill both new quadratic rows.
No search for a representation or additional sign witness is necessary.

Conversely, the small-error argument recovers every old power meaning and
therefore an integer quotient for each deleted congruence. Soundness of the
whole arithmetic construction uses this recovered meaning and the retained
inherited proof. The separate strict-horizon and beta changes use cofinal completeness;
they are not claimed to be bijections at each fixed old horizon.

## 6. Literal implementation review

The producer compares every old power residual to the signed error polynomial
plus or minus the old modulus times its private quotient. It independently
matches the retained equations Z_i=A*Y_i and the Pell norms. In particular,
the actual center is stored `shared.A` plus one, q is `pow2.output` minus
one, each actual X_i is its stored coordinate plus one, and two special Y/Z
coordinates have explicit recorded shifts. These shifts are necessary.

It refuses deletion if any removed modulus or quotient occurs in a retained
row. Its optional norm reduction is accompanied by the exact difference of
the retained norm rows. The principal variant retains the original odd Pell frame. The optional
stronger-frame experiment must not be confused with a necessary hypothesis
of the square-frame proof above.
