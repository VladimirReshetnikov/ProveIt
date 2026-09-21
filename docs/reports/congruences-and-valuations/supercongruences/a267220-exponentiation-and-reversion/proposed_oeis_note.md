# Proposed explanatory note for A267220

**Draft only — not submitted to OEIS.** Bibliographic identification of the article should be supplied before submission or adapted to the eventual publication details. The general framing principle is prior work of Schwarz, Vologodsky, and Walcher.

Both of the October 17, 2024 supercongruence conjectures follow from framing of the Apéry 2-function. With the OEIS generating function denoted by A, define

    B_t(n) = [x^n]A(x)^(t*n)/t  for nonzero integer t,
    B_0(n) = A005259(n),        for n >= 1.

Then B_t(n) is always an integer, and, for every odd prime p and p | N,

    B_t(N) == B_t(N/p)  (mod p^(2*ord_p(N))).

Lagrange inversion gives

    u_m(n) = m*B_m(n),
    v_m(n) = m*B_(m-1)(n).

Thus both conjectures hold also for p=3. For nonzero m, the odd-prime congruence has the stronger exponent `2*ord_p(N)+ord_p(m)`.

At p=2 the normalized difference has valuation at least `2*ord_2(N)` for even t and at least `2*ord_2(N)-1` for odd t. Consequently the conjectured congruence for v_m holds for p=2 as well, for every integer m: either m is odd and m-1 is an even framing, or m is even and the prefactor m compensates for the possible one-power loss. The case m=0 is immediate.

The analogous uniform extension for u_m is false: u_1(2)-u_1(1)=118 is not divisible by 4. A uniform cubic modulus is also false in both families; at p=7, u_1(7)-u_1(1)=5082313271 has valuation exactly 2, and v_2(n)=2*u_1(n).

The accompanying article contains an elementary binomial-product proof of the seed congruence, a full formal proof of the framing step, all parameter edge cases, and reproducible exact checks.
