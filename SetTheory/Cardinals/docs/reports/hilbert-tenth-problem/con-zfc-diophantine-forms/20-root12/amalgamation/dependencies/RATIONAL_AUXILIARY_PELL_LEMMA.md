# Rational auxiliary Pell-root integrality

Independent review, 22 October 2026. Verdict: **the proposed lemma is true**, including signed V and y. No coprimality hypothesis on I and V is needed.

## Exact statement

Let I,V be integers with I >= 2, and let y be rational. If

    (I V)^2 - (I^2 - 1)y^2 = 1,

then y is an integer.

The hypothesis that the first coordinate is a multiple of I is essential. For example, I=7 and y=1/4 give 2^2-(7^2-1)(1/4)^2=1, but 2 is not a multiple of 7. Thus the weaker assertion “integral first coordinate implies integral y” is false.

## Self-contained proof

Write I^2-1=d s^2, with s a positive integer and d a positive squarefree integer. Since I^2-1 lies strictly between (I-1)^2 and I^2, d>1. Put x=|IV| and z=s|y|. Then

    x^2-d z^2=1.

First z is an integer. Indeed, if z=a/b is in lowest terms with b>0, then d a^2=b^2(x^2-1); hence b^2 divides d, and squarefreeness gives b=1. Also x>=I>=2 and z>0.

We briefly establish the only Pell classification needed. Among the positive integral Pell solutions choose the one with least real value epsilon=x_1+z_1 sqrt(d)>1; it exists because I+s sqrt(d) is one such solution. Every positive integral solution alpha=x+z sqrt(d)>1 is epsilon^n for some positive integer n. To see this, choose n with 1<=alpha epsilon^(-n)<epsilon. The quotient is still an integral expression X+Z sqrt(d), with norm 1, and its conjugate is its positive reciprocal. Consequently X>=1 and Z>=0. If the quotient exceeds 1, it contradicts the minimality of epsilon; hence it is 1. This also proves the same statement for I+s sqrt(d).

Write

    epsilon^j=x_j+z_j sqrt(d),
    I=x_m, s=z_m,
    x=x_n, z=z_n,

where m,n>=1 and x_0=1,z_0=0. The sequence x_j is strictly increasing for j>=0. The multiplication identities give

    x_(2m)=2 I^2-1 == -1 (mod I),
    z_(2m)=2 I s == 0 (mod I),
    x_(j+2m) == -x_j (mod I).

For 0<=r<=m, multiplication by epsilon^(2m) of epsilon^(-r) also gives

    x_(2m-r)=x_(2m)x_r-d z_(2m)z_r == -x_r (mod I).

Reduce n modulo 2m, to a remainder r in [0,2m). If r<m, then 1<=x_r<I, so x_r is not divisible by I. If r>m, use the second congruence to reduce to 2m-r<m, with the same conclusion. Since I divides x_n, the only possibility is r=m. Thus

    n=(2q+1)m

for some q>=0. Finally, expanding

    epsilon^n=(I+s sqrt(d))^(2q+1)

shows that its sqrt(d)-coefficient z_n is divisible by s. Therefore |y|=z_n/s is an integer, as required.

## Stronger conclusion

The same proof shows that every solution in the lemma is a genuine integer Pell solution for parameter I at a positive odd index:

    |IV|=chi_I(2q+1), |y|=psi_I(2q+1).

This is exactly the form needed for the odd quotient/congruence argument in the upstream signed-domain proof. The fundamental unit for d need not equal I+s sqrt(d), and the proof above explicitly handles that otherwise dangerous gap.

## Application and source boundary

In the normalized strong construction, after recovering f^2=1+Delta i^2 c^4, set I_aux=Delta |i| c^2. This is an integer >=2, and Q=I_aux^2. If the elimination recovers a rational y satisfying

    Q V^2-(Q-1)y^2=1

with V integral, the lemma proves y integral before applying the inherited signed Pell congruences.

The elementary proof above is new work in this review and does not rely on a numerical scan. Its application uses the exact normalized auxiliary norm in these pinned source documents:

- [Root amalgamation proof, section 2](https://github.com/VladimirReshetnikov/ProveIt/blob/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/09-combined13/proofs/ROOT_AMALGAMATION_PROOF.md).
- [Signed-domain proof, signed auxiliary quotient](https://github.com/VladimirReshetnikov/ProveIt/blob/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/14-integer29/proofs/signed_domain_proof.md).

These source copies were inspected directly and are included under the package root at `arithmetic/sources/`. This is ordinary arithmetic suitable for formalization, not a new proof-assistant certificate.
