# Two quadratic rows for any fixed-base block of Pell powers

Prepared in the present AI-assisted research iteration. This is an ordinary
unbounded arithmetic proof; the checker verifies its finite polynomial
identities and exact instance data, not the whole argument in a proof assistant.

## The local lemma

Let W>=258 be an integer, let A be an integer with |A|>W^W, and suppose
r<=15. Let n be a nonzero integer. For each i let m_i and k_i be integers,
with n^2<W, m_i^2<W and k_i^2<W. Let X_i,Y_i be the canonical signed Pell
coordinates at parameter A and signed index k_i, and let Z_i=A Y_i.
Thus the usual Pell group map sends X_i+(n-A)Y_i to n^{k_i} modulo
T=2An-n^2-1. Negative powers are meaningful modulo T because
T=-1 modulo n, hence gcd(n,T)=1.

Set D_i=m_i-X_i+Z_i, H=sum_i Y_i(m_i-X_i), and
S=sum_i(D_i^2-Y_i^2). The following identity holds:

    sum_i(D_i-nY_i)^2 = S-2nH-T sum_i Y_i^2.       (1)

All n,A,m_i,X_i,Y_i,Z_i in the application are existing coordinates or
affine coordinate expressions. Introduce only two new unrestricted integer
coordinates K,L, with quadratic rows

    K - 2 sum_i Y_i(m_i-X_i) - (2A-n)L = 0,        (2)
    sum_i[(m_i-X_i+Z_i)^2-Y_i^2] - nK + L = 0.    (3)

Eliminating K mathematically gives S-2nH=T L. In particular T divides the
left side of (1). Neither a coordinate for T nor a coordinate for H occurs
in the emitted polynomial.

Put b=floor(sqrt(W-1)). Every |n|,|m_i|,|k_i| is at most b, and b>=16.
Multiplication by n^b clears every negative Pell index. Consequently T
divides the nonnegative integer

    E=sum_i[m_i n^b - n^{b+k_i}]^2.

For n=1 or n=-1 this notation uses only nonnegative powers because
b+k_i>=0. Each summand is at most 4 b^{4b}, so

    0 <= E <= 4r b^{4b} < W^{2b+1} <= W^W.        (4)

Here 4r<=60<W, b^2<W, and 2b+1<=b^2+1<=W.
Also

    |T| >= 2|A||n|-n^2-1 >= 2|A|-W > W^W.        (5)

The only multiple of T in the interval in (4) is zero. Thus every term of
E vanishes and m_i=n^{k_i}. If |n|>=2, a negative k_i would imply the
impossible integer equality m_i n^{-k_i}=1. Hence k_i>=0 in that case.
For n=1 or n=-1, the exact signed-index unit output is recovered, with no
claim that the index is nonnegative.

Conversely, if m_i=n^{k_i} with all relevant integer outputs, canonical
Pell congruences imply T divides each D_i-nY_i. Identity (1) makes
L=(S-2nH)/T integral, and (2) defines an integral K. Equations (2),(3)
follow. This proves the fixed-base block equivalence under the stated
frame and canonical-pair hypotheses.

The original frame is sufficient. No enlarged frame, new exponential
predicate, variable exponent in the final polynomial, or extra inequality
is needed. The quantity b and the powers in (4) occur only in this proof.

## Instantiation and noncircular order

The principal source has eleven power requests at base q+1 and, after the
strict-horizon change, three requests at base q. Replacing each block by
(2),(3) deletes its individual quotient coordinates and its old modulus
coordinate. The savings are 11+1-2=10 and 3+1-2=2 coordinates and rows.

The exact input to this stage is `stages/basis238/equation.json`.
`inputs/square_frame_atoms.json` supplies a literal verified identity

    W=2+sum_{j=1}^{36} atom_j^2.

Every base, proposed output and requested index in the two blocks is one
of those 36 affine atoms. The index for the factorial binomial numerator
is the affine expression t+F^2; it is explicitly included. Since
`t=16+z^2`, the identity implies W>=258. The inherited Pell-frame and
orientation-first argument supplies |A|>W^W and canonical signed pairs
before any deleted arithmetic signs are used.

The first three power requests remain individual: the request producing
V=(F^2+1)^t, the request N=B^x, and the request q=(BH)^x. The rounded
factorial rows and common remainder norm first give B!=0, |B|>=2,
|F|<|B| and V<|B|^2. The multiplier H is odd, hence |BH|>=2.
The retained individual B and BH requests therefore give x>=0 and q!=0.
The q block can now be interpreted by the local lemma, including the
possible unit case q=1. If x=0, it gives M=q^x=1, contradicting the
unchanged identity B*d=M and |B|>=2. Therefore x>=1 and |q|>=2.
The retained ratio q^t*v=M=q^x gives x>=t, so |q|>=2^t>=2^16.
In particular |q+1|>=2, and the q+1 block now gives nonnegative requested
indices and their exact powers. This restores the ordinary factorial,
CRT-representative and strict-range interpretation.

The cofinal completeness proof constructs the same true powers and
canonical pairs as the incoming source (with the strict horizon and
linear beta-base choices proved separately). The converse direction of
the local lemma supplies the four new pooled coordinates. This is why the
pooling does not assume q's large sign or the representatives' signs before
it has justified them.

## Literal checks and coordinate offsets

`pool_certificate.json` records each removed power row, quotient and
modulus; each retained A*Y and Pell-norm row; and every affine expression
used. The old centered q coordinate represents q+1; its actual q is one
less. Canonical X coordinates have offset +1. The Y coordinate of pair3
has offset -1, and the stored A*Y coordinate of pair12 has offset +1.
The producer and independent verifier check these exact identities.

The verifier also checks (1) as a polynomial identity modulo only the
listed Z_i-A Y_i rows, and verifies all 14 base/output/index memberships
in the square frame. This supplements the ordinary proof rather than
replacing the unbounded estimate or inherited canonical-index theorem.

