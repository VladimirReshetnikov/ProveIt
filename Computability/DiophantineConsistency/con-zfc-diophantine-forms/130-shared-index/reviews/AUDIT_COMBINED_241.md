# Independent audit of the 241-variable natural quartic

## Verdict

The combined construction `../direct/equations/principal241` has a sound ordinary
arithmetic proof over the nonnegative integers. The enlarged shared Pell
cap, the shared factorial/CRT binomial, the new radix
`q=N(S+1)^K`, the amplification `K=R`, and the minimum horizon 12 are
compatible. No fatal error or unfilled new arithmetic premise was found.

The proof remains relative to the explicitly inherited complete
indexed-Pell criterion, the finite source encoding/CRT lemmas and the
C222-to-ZFC refutation calibration. This audit is not a new complete
Lean/Rocq/internal-ZFC derivation and does not prove consistency itself.

The raw arithmetic graph checked here has SHA-256
`d7bd1b63939e6c9e6887b88770c3fcacb7ba352dee61fb27155f51bed4d400a0`.

## 1. The shared cap remains valid after enlarging the semantic frame

The literal frame contains 25 distinct semantic atoms, including all
modular upper indices, and all 15 seed exponents are positive from their
raw natural gate definitions. Thus each is below `W`, and their count is
at most `W-2`. The adjustable base is `A=L+sigma`, where `L` satisfies
the lower-scale norm at base `W+1`. Consequently `A-1>W^3`.

The anchor retains the entire inherited positive index certificate. Its
usual assumption `Y_cap>=W` is supplied by the aggregate row. Each seed
norm then has some nonnegative index `j_i<W`. Reducing the pooled error
row gives

    A-1 divides sum_i (j_i-k_i)^2 < W^3 < A-1.

All differences therefore vanish. The statement remains valid for a seed
whose unknown ordinate is initially zero: positivity of its prescribed
index is used only at the final equality. Completeness is obtained by
choosing the fresh anchor and principal pairs after the semantic frame;
the aggregate slack and error-square quotient are nonnegative.

The private base `A` is still chosen in the common-root residue class
after `W` and the semantic radix are fixed. No private anchor coordinate
appears in that frame, so this order is noncircular.

## 2. Uniform coefficient lemma needed for the new bootstrap

For every integer `rho>=1`, `t>=0`, and `0<=j<=t`,

    binom(rho+t,j) <= (rho+1)^t.

An induction on `t` proves this without an assumption `rho>=t`.
At `j=t`, write the binomial as
`product_(i=1)^t (rho+i)/i`; every factor is at most `rho+1`.
At `0<j<t`, Pascal's identity and the induction hypothesis bound it
by `2(rho+1)^(t-1) <= (rho+1)^t`. The endpoints `j=0` and `t=0`
are immediate. This is the correct uniform bound; appealing to
monotonicity in the lower binomial index would require a stronger,
unavailable hypothesis on `rho`.

## 3. The new radix is certified before interpreting the shared binomial

After the shared cap has established the six exact powers, the unchanged
factorial rows give

    V0=(F^2+1)^t,       V0+s=B F,       B=r+s+1,

with all letters natural. Because `V0>=1`, one has `F>=1`. Also
`V0>F^2`, whence `F^2<B F` and `F<B`. Therefore

    V0 <= B F < B^2 <= B^K=N < N(S+1)^K=q.

The last strict inequality is valid because `S` is the sum of nine
strictly positive independent representatives. The raw budget has
`K=2+t+x+y+F>=2`; the actual checked minimum is already at least 14
before the factorial meaning is recovered.

Apply Section 2 with `rho=F^2`. Every coefficient needed for the shared
factorial/CRT binomial is below `q`. Its exact digit consequently gives
`B=binom(F^2+t,t)`. The inherited squared-radius fixed-point theorem
(valid at least for `t>=6`) then gives `F=t!`. Only after this point is
the reciprocal CRT meaning of `B` used.

Thus deleting `V0` from the radix base is licensed by the literal
ceiling rows. It does not assume the factorial answer in advance.

## 4. All remaining digits fit without an aggregate representative bound

Each of the nine ordinary upper arguments is at most `S`. Its lower
index belongs to `{t,t+1,x+1,y+1}`, is positive, and is less than `K=R`.
Thus all relevant lower coefficients are at most `max(1,S^k)<q`.

The derived label polynomial satisfies the inherited literal majorant
`J <= (S+1)^ell`, where `ell=4194304`. Once `F=t!`, the horizon-12
budget proves

    3 ell(t+1) <= 2F,       ell(t+1) < F < R=K.

At `t=12`, the displayed inequality is
`163577856 < 958003200`; induction in `t` follows because factorial
growth dominates `t+1`. Hence every required derived lower coefficient
is also below `q`. The common-root modulus retains its denominator
product, and `N` divides `q`, so every exact and divisibility modulus
still divides that product.

The local arithmetic source bound is unchanged, with `E=8388608`.
Since `12! =479001600 >2^28` and `28E<2^28`, the usual elementary
integer induction gives `R^E<2^R=2^K`. Thus both local evaluation and
derived-label recovery retain the needed prime-power interval bound.
Every range lower index is less than `K`; the old precision-`2K`
completeness proof therefore loses fewer than `K` valuation digits
when dividing by its factorial.

## 5. Completeness and calibration

Choose a padded finite C222 proof horizon first, then its factorial,
formula weights, beta code, reciprocal product and `N=B^K`. Choose the
nine representatives at precision `2K`, raising each by a multiple of
`N^2` if needed. Define `S` and `q` from those actual representatives.
No upper-bound slack on their sum is required. The carry bounds above
provide the true digit remainders and nonnegative quotients.

Now compute the enlarged semantic frame `W`. Choose `L` from its lower
Pell norm and choose a sufficiently large `A>=L` satisfying the modular
root congruence. This linear congruence is solvable because its modulus
is a power of `q`, coprime to `q+1`; the possible factor 2 divides the
right side whenever it divides the modulus. Supply the full anchor,
canonical principal pairs and all remaining natural private quotients.
The existing contraction restores every eliminated natural coordinate.

The converse follows the reverse semantic order: cap, exact powers,
bootstrap factorial/binomial, remaining digits, prime-power decoding,
Horn-flow refutation, and the named inherited ZFC calibration.

## 6. Exact independent checks and limits

The portable `../direct/code/audit_combined.py` in self-radix mode imports neither the builder
nor the contraction code. It passes **225 exact checks**, including:

- all cap, norm, enlarged-frame and positivity boundaries;
- equality of the calibrated source hash and the local-majorant
  certificate with the shared-binomial parent;
- preservation of seven semantic source rows modulo gate renaming and
  the deliberate horizon shift;
- preservation of all ten range requests;
- the literal formulas for `F^2`, `R`, `S`, `N`, the radix and shared binomial;
- all six exact-power congruences and their modulus definitions;
- all eleven modular digit rows, remainders, denominator identities and
  the common-root denominator product;
- the numerical base cases of the horizon-12 budgets.

These checks bind the ordinary proof to this raw arithmetic graph. The
separate contraction checker establishes the exact final coefficient
list. Neither finite checker replaces the unbounded arithmetic proof or
the inherited logical calibration.

The final selected equation has 241 natural variables, 189 quadratic
residuals, 30,058 expanded quartic monomials and height 85,187,728. All
four counts improve on the inspected 261-variable parent (261, 194,
31,679, 85,566,955). This is a concrete relative improvement, not a
claim of a global minimum or worldwide priority.
