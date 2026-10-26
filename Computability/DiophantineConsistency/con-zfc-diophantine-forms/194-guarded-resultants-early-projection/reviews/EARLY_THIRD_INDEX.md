# Early exclusion of the third main Pell index

This is an ordinary arithmetic lemma for the free-quotient positive chart. It does not assume that the decoded rank equals the main Pell index, or that q divides Y.

Assume integers q>=73, X>=q with q|X, Y>=1, k>=2 and 0<eta<k, and put

    c=kY+eta, A=qY(X+1)+1, v=Xq²Y²,
    H=4A-5, K=X(3c-2X)+2.

Suppose c=psi_A(p) for a positive odd p, k=2psi_(1+2v)(m) for m>=1, and H divides 6(q-1)K. Then p>=5.

First c>=3 excludes p=1. If m=1, k=2 and the positive strip gives eta=1, so c=2Y+1 lies strictly between psi_A(1)=1 and psi_A(2)=2A. No main index can have this ordinate. Thus m>=2. Also 1+2v>A, and monotonicity would give k/2>=c if m>=p, contrary to c>k. Hence m<p.

Suppose p=3. Then m=2, k=8Xq²Y²+4 and c=4A²-1. With u=X+2-2Y, direct expansion gives

    eta=4q²Y²(Xu+1)+8qY(X+1)-4Y+3.

If u<=-1, this is at most

    4qY[-qY(X-1)+2(X+1)]-1 < 0,

since qY>=73 and X>=73. If u>=2, subtraction of k leaves at least

    4q²Y²+8qY(X+1)-4Y-1 > 0.

Both contradict the strip. Thus u is0 or1 and 2Y is X+2 or X+1.

Because 4A=5 modulo H, one has 4c=21 modulo H and therefore

    4K=-(X-8)(8X+1) modulo H.

The assumed divisibility implies H|N for

    N=6(q-1)(X-8)(8X+1)>0.

Now H=4qY(X+1)-1>=2q(X+1)²-1>2qX², whereas
N<48qX². Consequently a=N/H is an integer satisfying0<a<24.
Reduction modulo q uses X=0, H=-1 and N=48, giving a=-48 modulo q.
Thus q divides a+48, an integer between49 and71, impossible for q>=73.
This proves p>=5.

Application boundary: root extraction and signed all-index folding supply c and k before transport. Integral carrier z=Z/M gives H|6(q-1)K directly from the literal numerator, since D=6q^7 and gcd(q,H)=1. Any integer polynomial carrier shift M*Omega leaves this divisibility unchanged. In a norm scaled by a fixed integer r, adjacent-Pell descent still gives z=±r*g*y integral, so the same argument applies. The actual historical and low-padding coefficient tuples have beta far larger than73; this stronger numerical hypothesis must be stated rather than silently using only the older beta>=31 box.

Once p>=5, c>c3=4Delta+3. The unsquared trace identities for auxiliary index3 are f(b-4Delta f)=c-c3 or f(b+4Delta f)=c+c3. Both right sides are strictly between0 and2c<f, excluding that index without assuming a sign for b. The ensuing stronger lower bound on |b| may therefore be used to justify squared transport, subject to the remaining explicit carrier estimates.

This is not a consistency assertion or a finite-test proof of an unbounded statement. It is an algebraic/inequality lemma composed with the identified inherited Pell classification and native calibration.
