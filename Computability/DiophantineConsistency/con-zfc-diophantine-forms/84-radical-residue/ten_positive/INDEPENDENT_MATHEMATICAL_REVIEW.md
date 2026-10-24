# Independent mathematical review of the ten-positive-variable reduction

Review scope: the new unbounded arithmetic proof in `PROOF.md`, checked against the literal high-level formulas in `build.py` and the exact inherited source61 statements. This is a separate review within the AI collaboration. It is not external human peer review, a full native-tableau reproof, or a new Lean/Rocq certificate. The literal four-root norm and degree/circuit computations are checked separately.

Repository pin: `c1a102936aca437e9999530a0111e6ddab56dc6d`.

## Verdict

The reviewed new existence reduction is mathematically sound, subject to precisely the inherited compact44 native/compiler and refutation-calibration statements identified by the author. In particular, the two principal gaps identified in the incoming `pell/FOUR_ROOT_LIMITS.md` are both repaired: all signed subset sums are excluded by an unconditional hierarchy, and the mixed residue is separated using a strict bound rather than a false coprimality cancellation.

No additional divisibility or cofinality condition on canonical `Y` is imposed. The argument does not assume consistency, arithmetic soundness of ZFC, a positive main-root sign before proving it, or the omitted transport divisibility before restoring it.

## 1. Four radicals, including the smallest root

Use the author's notation, with `s=Y/q^3` for the actual tenth-input list (the proof initially calls this coordinate `y0`). For every positive input tuple, `q>=16`, `Y>=q^3`, `k>=2`, `c=kY+eta`, `a=(X+1)Y`, and `Delta=(a+2)^2-1`.

The fourth positive root is `d/H`, not `d`, where `d^2=1+Delta*c^2` and `H=4a+3`. This distinction is essential: `d/H<c`, while the first root `t` satisfies `t>ell=XY^2*k>2c+1`. Also `f>(a+1)c^2` and `t<(a+1)c`, so `f-t>(a+1)c(c-1)>2c+1`.

Writing `b=cT-R` gives exactly two cases, without a `C>0` assumption:

- If `b=0`, then `V=-c`, `c<y<c+1`, and the ordered roots are `d/H,y,t,f`, with each after the first larger than the sum of its predecessors.
- If `b!=0`, then `|V|>=f^2-c`, `y>|V|>2f`, and the ordered roots are `d/H,t,f,y`, again with each later root larger than the preceding sum.

Thus every nonempty signed subset sum is nonzero, including the three-root subsets omitted by the failed incoming argument. The square-class extraction proof is valid: in the generated multiquadratic field, distinct square classes yield distinct characters; averaging isolates the contribution from each nontrivial class. A nonempty nontrivial class would have a forbidden signed subset sum. Therefore every root is rational at a rational norm zero.

The integer radicands make `tau_*,f_*,d_*` integers. The last root satisfies the adjacent-coefficient Pell equation `Q V^2-(Q-1)y_*^2=1`, with `Q>1` and integer `V`, so the supplied descent proves it integral. No denominator cancellation involving `H`, `q`, or `q-1` is being smuggled into this step.

## 2. Positivity before the mixed residues split

The proof-only coordinates `r,gamma` may initially be rational. The triangle estimate

`|gamma| <= d/H + (X+ac)/H + X/q + |k-R-1|/q^5 < Gbar`

uses only positive inputs and the unconditional bound `|R|<Rhat`. Together with `f+y<3Vbar` and `L=3Vbar+Gbar`, it gives

`r=n+L-f_*-y_*-gamma>0`.

The identity defining `r` then yields `W Bt/(q-1)>s+r>0`, hence `Bt>0`. Since `q K0+X>0`, a nonpositive `C` would make `(qK0+X)C-qF<0`. Thus `C>0` is established before using the native rank bound `3q<R<q^4-2`.

This order is valid over the real/rational proof coordinates. Integrality of `r` is not needed to establish its positivity or the positivity of `C`.

## 3. The strong and auxiliary indices really precede the q-power residue

The positive roots give `c=psi_A(p)` and `k=2 psi_P(m)`, where `A=a+2` and `P=2XY^2+1>A`.

Because `c>1`, `p>=2`. If `m=1`, then `k=2` and positivity of `eta,zeta` forces both equal to 1, so `c=2Y+1`. This contradicts `c>=psi_A(2)=2A>2Y+1`. Therefore `m>=2`. It follows that

`k>=4P>8XY^2`, `c>8XY^3>8q^9>2R`.

Also `m<p` and `c>2p`. These estimates use only supplied `X>=1`; they do not assume `q|X` or `X=2^R`.

The source61 report's **Direct normalized rank** lemma (`lem:rank`) requires exactly `c=psi_A(p)>2`, `f^2-Delta I^2=1`, and `c^2|I`. It proves `pc|m_strong`, so `c|m_strong` and `m_strong>2p`. The brief proof is classification, strong divisibility, and the congruence `psi_D(v)=vD^(v-1) mod c` for `D=chi_A(p)`; no earlier main-root orientation enters.

For the source61 **Signed auxiliary-index recovery** lemma (`lem:index`), set `S_aux=Delta I`. Then `S_aux^2=Delta(f^2-1)`, `c|S_aux`, and `S_aux>=2`. The congruences are

`V=-c mod f`, `V=-R mod c`.

The latter uses `f^2=1 mod c`. All interval hypotheses `0<p,R<c/2` have already been checked. The lemma explicitly allows arbitrary signs of `V,y`, and explicitly excludes any requirement of a main-root congruence or deleted index quotient. Therefore its conclusion `p=R` is available at precisely the place the author uses it. This resolves the principal possible circularity.

## 4. Exact q-power recovery from the mixed equality

The four-root equality makes `r+gamma` integral, because `n,L,f_*,y_*` are integers. Clearing the still-mixed denominators gives

`q^5 | H(q-1)(q^4X-v)`.

Since `Y=q^3s`, `H=3 mod q`. The actual coefficient slice and `J=3j+1` give `q=2 mod 3`; hence `gcd(q,H(q-1))=1`. Thus `q^5|q^4X-v`.

The first-Pell recurrence and `q^4|4XY^2` imply `q^4|2m-R-1`. From `1<=m<p=R<q^4`, the absolute value of this expression is strictly smaller than `q^4`. It is zero, giving `R=2m-1`. The positive number `v=k-2m` is a multiple of `4XY^2`, hence of `q^5`, so the previous divisibility gives `q|X`.

The now-integral q-power quotient leaves

`H | (q-1)(d_*-X-ac)`.

This is the exact weaker conclusion. The proof does not cancel `q-1` from it.

## 5. The size argument resolves both sign and residue

Put `r0=m-1=(R-1)/2`. The elementary Pell growth estimates and

`(2A-1)^2-2PX = 4Y^2(2X+1)+12Y(X+1)+9-2X > 0`

give `c/k>X^r0/2`. Since `c/k<Y+1` and `X>=q`,

`Y>q^r0/2-1>q*2^R`.

The last bound already holds for `q>=16,r0>=4`; the available `R>3q` gives the stronger `r0>=24`. In particular, this bound is obtained before identifying `X` with `2^R`.

Let `T0=2^R`. The main Pell polynomial congruences are valid modulo `H` because `Delta=a^2 mod H`:

`chi_A(R)-a psi_A(R)=T0 mod H`,

`T0(chi_A(R)+a psi_A(R))=1 mod H`.

If `d_*=-chi_A(R)`, the weak residue implies `H|(q-1)(1+T0 X)`. This is impossible because the dividend is strictly between 0 and `H` by the new bound for `Y`. Thus `d_*>0`.

For the positive sign, `H|(q-1)(T0-X)`. Its absolute value is strictly smaller than `H`, again by `Y>qT0`. Therefore it is zero and `X=T0`. The unmultiplied main residue follows from the first Pell congruence. This proves the actual needed divisibility `H|(d_*-X-ac)` without requiring `gcd(H,q-1)=1`.

Now `gamma` is an integer, so `r` is an integer. Its defining equation gives `(q-1)|W Bt`; since `W=1 mod(q-1)`, the exact transport divisibility follows as well.

## 6. Reconstruction and completeness checks

All recovered source coordinates are positive integers. In particular `w=X/q>0`, `h=v/(XY)>0`, and `gamma_old=(d_*-ac-X)/H>0`, using `d_*>(a+1)c` and `c>X` (the latter follows, for example, from `Y>qX`).

The two easily missed shifts are correct:

- `T_old=f_old*T` gives `c(T_old*f_old-1)-R*f_old^2 = f_old^2(cT-R)-c = V` exactly.
- With `z_new=((K0+w)C-F)/(q-1)>0`, set `z_old=z_new+1`; then `(K0+w)C+(q-F)-z_old(q-1)=1` exactly.

Source61 `positive/PROOF14.md` explicitly supplies canonical `J=1+B+...+B^(N-1)` with `N=581197^n>1` odd. Since `B=2^590069=2 mod3`, this ensures `J=1 mod3` and `j=(J-1)/3>0`. The positive auxiliary reconstruction lemma applies to every retained positive strong pair with `c|I`, so replacing the auxiliary parameter by the canonical positive `T` is licensed.

Canonical `Y=q^3s` already supplies the new positive input `s`. No additional condition such as `(q-1)|Y` is used. The canonical transport quotient satisfies `t0>=q` and `s<k`. Consequently the chosen `r` exceeds `qW-2k>2L`. Even if the proof-only `gamma` is negative, `|gamma|<Gbar<L` makes the chosen integer `n=r+gamma+f+y-L` positive. Thus every supplied input in the reverse construction has the required strict positivity.

## 7. Polynomial and formalization boundary

The actual circuit uses `M=(q-1)q^5`. Its integer carrier divided by `M H` equals exactly the rational `Z` of the proof. Its four norm radicands are `(MH)^2 Dt`, `(MH)^2 Df`, `M^2 Dd`, and `(MH)^2 (Q V^2-1)/(Q-1)`. All cleared denominators are strictly positive on the declared input domain, so clearing them adds no zero branch.

The new reduction is ordinary mathematics formalizable in ZFC, using only the explicitly stated inherited source calibration at its final endpoint. It introduces no consistency assumption. The source's ongoing formalization of native calibration and all nonstandard internal proof codes remains separate. Circuit replay establishes its literal polynomial and finite algebraic identities; it does not replace those unbounded statements.
