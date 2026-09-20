# Compact certificate: the prime 2749 refutes the height-2 conjecture

Let T_0=1, T_(h+1)=2749^(T_h), D_h=T_(h+1)-T_h, and
C(h)=min(v_2(D_h),v_5(D_h)). The source's speed at height h is
V(2749,h)=C(h)-C(h-1), not C(h+1)-C(h).

## Primality and membership

The primes at most floor(sqrt(2749))=52 are
2,3,5,7,11,13,17,19,23,29,31,37,41,43,47.
The corresponding remainders of 2749 are
1,1,4,5,10,6,12,13,12,23,21,11,2,40,23.
None is zero, so 2749 is prime. It equals 275*10-1, hence belongs to the prime set specified in the conjecture.

## Exact valuations

2749-1 = 2^2 * 3 * 229.
2749+1 = 2 * 5^3 * 11.

All towers are odd, so all D_h are even. For h>=1,

    D_h = 2749^(T_(h-1)) * (2749^(D_(h-1))-1).

The first factor is coprime to both 2 and 5. Binary lifting gives an increment of
v_2(2748)+v_2(2750)-1 = 2 in v_2(D_h).
Odd-prime lifting applied to 2749^2, with even exponent D_(h-1), gives an increment of 3 in v_5(D_h).
The initial values are v_2(D_0)=2 and v_5(D_0)=0. Therefore

    v_2(D_h) = 2 + 2*h,
    v_5(D_h) = 3*h,
    C(h) = min(2 + 2*h, 3*h).

It follows that C(0),C(1),C(2),C(3),... = 0,3,6,8,10,...
and V(2749,1),V(2749,2),V(2749,3),... = 3,3,2,2,...
Thus V(2749,2)=3, while the permanent speed is 2. This disproves the conjecture exactly in its original height convention.

## Why no smaller prime works

The general theorem says a base ending in 9 fails the bound exactly when
s=v_2(a-1)>=2 and s<e=v_5(a+1)<2*s.
Thus 250 divides a+1 and a is 1 modulo 4.
Below 2749, the only possible bases are 249,749,1249,1749,2249.
Only 749 and 1749 satisfy the valuation inequalities; they factor as 7*107 and 3*11*53.
So 2749 is the smallest prime counterexample.

## Source and status

The claim is Conjecture 2, journal page 57, in Marco Ripà,
*The congruence speed formula*, NNTDM 27(4) (2021), 43–61;
it is Conjecture 4.1, page 14, in arXiv:2208.02622v1.
This certificate is an unrefereed proof, not a claim of verified priority.
The elementary lifting lemmas are proved in full in the accompanying article.
