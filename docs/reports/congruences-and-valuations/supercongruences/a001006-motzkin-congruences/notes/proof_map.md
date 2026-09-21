# Proof map

Notation: P=x^(-1)+1+x; Q=1-x^2; T_n=CT(P^n);
U_n=[x]P^n; M_n=CT(QP^n).

## Shared mechanism

Reflection of the initial segment of a bad path gives M_n=CT(QP^n).
The support of QP^d lies in [-d,d+2].

Frobenius plus the elementary implication
A=B (mod p^a) => A^p=B^p (mod p^(a+1)) yields
P(x)^(p^k)=P(x^(p^(k-s+1)))^(p^(s-1)) (mod p^s).

For h=m*p^(s-1) and q=p^(k-s+1), only the exponent zero in QP^d
can interact with the large factor for d<=q-3. The two final offsets
contribute respectively -U_h and -(q-1)*U_h. This is Theorem 3.3.

## Bala targets

B3: Set s=m=1. T_1=U_1=1. The next offset gives defect -1 (mod p).

B1/B2: The reciprocal 1/(1+x+x^2) has coefficient period (1,-1,0).
Since Q/(1+x+x^2)^2 is the derivative of x/(1+x+x^2), it gives
M_(p^r-2)=(epsilon_p^r-1)/2 (mod p). Put m=n-1 and d=q-2 in the
block theorem. This proves the single boundary formula in Theorem 4.2,
and both targets are immediate cases.

B4: The block theorem with s=2 leaves T_(mp). Factor
1+x+x^2=(x+alpha)(x+beta) over sixth roots of unity. Each central
coefficient is a sum of squared binomial coefficients times root
powers. Terms with p not dividing the binomial index vanish mod p^2;
Babbage's congruence handles the remaining terms. This proves
T_(mp)=T_m (mod p^2), Theorem 5.2. Take m=1.

Sharp square endpoint: Use
2(N+1)U_N=N(T_N+3T_(N-1)) and set N=p. It gives
U_p=p(1+3*epsilon_p)/2 (mod p^2). The first omitted offset of B4
has defect -U_p, which is -2p or p and never zero mod p^2.

## External-dependency boundary

Sections 2–6 and the block theorem contain all necessary proofs and use
no unproved arithmetic assertion. Section 7.2 is an optional stronger
scalar reduction that cites Pan–Sun explicitly. The appendix gives
another self-contained proof of the scalar T_p=1 (mod p^2).

The Python run is a separate finite check, not a premise of any theorem.
