# Exact supporting checks

Date: 2026-10-03

All four replay commands in README.md pass. These tests are secondary evidence; the universal asymptotic and the full native bijection are proved mathematically in their respective theorem packets.

## Main checker

`../../check_total_bitlength.py` uses only the Python standard library and verifies the saved JSON receipt in normal mode. It checks:

- Eighteen exact auxiliary reconstructions, with A=3,4,5; p=3; and the exact progression M=pc/gcd(c,Δ). Each model includes baseline l=1,2,3; both nonbaseline signs in l=1,k=1; and l=2,k=1 on the minus branch
- Positivity and integer types of f,i,j,o,y, exact integrality of every quotient, both varying norm equations, and U=jc−p=of−c
- The exact product identity P c³=R y(U+p)(U+c), with P=fijoy
- Eighteen deliberate c²-denominator mutations, all detected
- Exact integer rounding inequalities 2^(b_var−5)≤P<2^b_var
- Fifty-four finite-sample cutoff sandwiches, immediately below, at, and above each of the eighteen sampled total-bit budgets
- Six direct rounding fixtures, including powers of two, and a synthetic rank-with-ties check

The seventeen fixed fixture coordinates are the arbitrary numbers 1 through 17; their bitlength sum is used only to test a constant shift. They are NOT asserted to be native forced coordinates. The cutoff counts enumerate just the finite eighteen-pair sample, not all admissible pairs. This deliberate limitation keeps the verification small and avoids pretending that finite checks prove the asymptotic.

## Independent checker

`../../check_total_bitlength_review.py` was written by the independent mathematical reviewer. With A=3,p=3,c=35,M=105 it checks nine exact auxiliary tuples: l=1,2,3 and n=p,4Ml−p,4Ml+p. It independently checks reconstruction integrality and positivity, the varying norms, exact product cancellation, and the equivalent integer bound

    0≤b(f)+b(i)+b(j)+b(o)+b(y)−b(fijoy)≤4.

Three direct fixtures cover rounding at powers of two and other integer boundaries. The largest independently checked varying-coordinate subtotal is 3,039,353 bits. No tuple is claimed to be a complete padded native instance.

## Replay discipline

Both scripts pass under `python3` and `python3 -O`. No Python assert statements are used for verification. Neither script imports or runs pinned upstream code. The main receipt is deterministic, all product comparisons are integer exact, and no floating-point logs or approximate floors decide a boundary. There are no numerical experiments advertised as proof of the second-order constant.
