# A linear-prefix coprime Pell stack

This is a new simplification of the square-stack lemma in package 29,
`SIGNED17_PROOF.md`, reviewed at ProveIt commit
8c6eec9d19ef80538c8e61ff6e0180040583446a.

Let d_1,...,d_k be integers congruent to 2 modulo 3. Define
C_0=1, B_j=1+4 d_j C_{j-1} z_j^2, C_j=C_{j-1} B_j.
Then

    all d_j>0
    iff there exist nonzero integers z_1,...,z_k with C_k an integer square.

This replaces the old C_{j-1}^2 in B_j by C_{j-1}.

## Soundness, including negative intermediate values

Each B_j is 1 modulo 4, hence nonzero. Moreover gcd(B_j,C_{j-1})=1.
Consequently the B_j are pairwise coprime and all C_j are nonzero. If C_k
is an integer square, unique factorization implies that every |B_j| is
an integer square. A negative integer square is 0 or 3 modulo 4, whereas
B_j is 1 modulo 4. Thus every B_j is a positive square. In particular,
every prefix C_j is a positive square. Since z_j is nonzero,
B_j=1+4d_j C_{j-1}z_j^2 would be at most -3 if d_j<0. Hence d_j>=0.
The congruence d_j=2 modulo 3 excludes zero, so d_j>0.

No prefix positivity is assumed before deducing that all individual
factors are positive squares.

## Completeness

Suppose all d_j>0. A positive integer congruent to 2 modulo 3 is not a
square. Inductively C_{j-1}=c^2 with c a positive integer. Choose a
nontrivial solution u^2-d_j v^2=1 whose v is divisible by 2c. Such a
solution exists: take a positive Pell unit and raise its determinant-one
integer matrix to a positive power that is the identity modulo 2c.
Then z_j=v/(2c) is a nonzero integer and
B_j=1+4d_j c^2 z_j^2=u^2. Thus C_j is again a positive square.
This finite induction constructs all witnesses.

## Degree and operation effects

For degree-one guard parameters d_j and degree-one witnesses z_j, the
old degree recurrence is c_j=3c_{j-1}+3, and the new recurrence is
c_j=2c_{j-1}+3. Thus six initial guards have degree 189 instead of 1092.
For a last guard d_7=3m-1, the final degree bound is deg(m)+380 instead
of the old bound. The exact old formula is deg(m)+3*1092+2 = deg(m)+3278;
the new formula is deg(m)+2*189+2 = deg(m)+380.
For the Jones instance deg(m)=2221 L+11, this gives deg(C_7)=2221 L+391.
These are exact when leading coefficients do not cancel, as they do not
in the displayed products with nonzero leading guard coefficients.
Each stage after the first saves the square of Cprev; the first stage
C_0=1 was already constant-foldable, so a live DAG saves six, not seven,
multiplications if all other evaluations remain unchanged.

The nonzero requirements on z_j are essential. They remain encoded in the
separate intersective divisibility construction, not inferred from C_k.
This lemma does not by itself reduce the number of quantified variables.

## Signed separator improvement

On the nonvanishing branch S!=0 in the intersective merger, every z_j is
nonzero. Also d_j!=0 and Cprev!=0, so B_j!=1. Since B_j=1 modulo4,
|B_j|>=3. For a nonempty guard stack, |C_k|>1, hence
|C_k|>sqrt(|C_k|). Thus the first separating weight may be C_k itself,
not C_k^2+1. Let w1=C_k and w2=C_k(P^2+K^2+2). The universal bound
sqrt(|(P^2-1)K^2+1|)<=P^2+K^2+1 gives
|w2|>sqrt(|C_k|)+|w1|sqrt(|a0|).
The Galois sign-separation argument uses absolute weights and is unchanged
for negative C_k. On S=0 the norm equals T^8!=0 independently of weights.
