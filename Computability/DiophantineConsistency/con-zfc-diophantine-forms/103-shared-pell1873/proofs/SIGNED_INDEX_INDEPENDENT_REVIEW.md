# Independent adversarial review of signed Pell-index coordinates

## Scope

This reviews precisely the signed-S/R optimization adopted for the frozen batched-Pell construction. A,B,X,Y,U and the exponent k retain their stated natural domains, with A,B>=2,U>=2,X,Y>0 and 0<k<=Y. S,R and V may be signed. The actual construction keeps B positive; no signed-base extension is asserted here.

The review inspects the literal pinned source `provenance/PellMatiyasevic.lean`, rather than relying on the informal name of a Pell theorem. It uses the published lemmas `eq_pell`, `yn_ge_n`, `strictMono_y`, `dvd_of_ysq_dvd`, `xn_modEq_x2n_add`, `modEq_of_xn_modEq`, `xy_modEq_of_modEq`, and `yn_modEq_a_sub_one`. Their exact statements support the proof below. The source's special low-index exception is already excluded by the positive target index and its upper bound.

## Statement checked

Assume

    X^2-(A^2-1)Y^2=1,
    U^2-(A^2-1)V^2=1,
    S^2-(B^2-1)R^2=1,
    V!=0,  Y^2 divides |V|,
    B=A modU,  B=1 mod4Y,
    S=X modU,  R=k mod4Y,
    0<k<=Y.

Then X=X_A(k) and Y=Y_A(k). In particular S and R need not be nonnegative. All displayed congruences are integer congruences; their moduli are positive under the hypotheses.

## Proof, including the changed sign branch

Natural Pell classification gives indices i,n,h>=0 with

    X=X_A(i), Y=Y_A(i),
    U=X_A(n), |V|=Y_A(n),
    |S|=X_B(h), |R|=Y_B(h).

Since Y>0 and |V|>0, i,n>0. As Y divides |V|, positivity implies Y<=|V|; strict increase of Y_A therefore gives i<=n. The stronger square divisibility and the exact Mathlib lemma

    dvd_of_ysq_dvd:
      Y_A(i)*Y_A(i) divides Y_A(n)  =>  Y_A(i) divides n

give Y|n. Also `yn_ge_n` gives i<=Y.

Because S is nonzero in a Pell norm, S=epsilon X_B(h), epsilon in {+1,-1}. Base congruence transfers X_B(h)=X_A(h) modU.

If epsilon=+1, the congruence S=X modU becomes X_A(h)=X_A(i) modX_A(n). The exact hypothesis of `modEq_of_xn_modEq` is i>0 and i<=n; no strict inequality is required. The conclusion is

    h=i mod4n  or  h+i=0 mod4n.

In either case h=+/-i mod2n.

If epsilon=-1, the same congruence gives X_A(h)=-X_A(i) modU. The exact anti-period lemma `xn_modEq_x2n_add` states

    X_A(2n+h)+X_A(h)=0 modX_A(n).

Consequently X_A(h+2n)=X_A(i) modU. Apply `modEq_of_xn_modEq` with j=h+2n, then reduce its result modulo 2n. Again h=+/-i mod2n. This shift is the essential extra argument; taking |S| without it would not preserve the original congruence.

Write R=delta Y_B(h), with delta in {+1,-1}; if R=0 either sign can provisionally be used. Since B=1 mod4Y, the Pell recurrence gives Y_B(h)=h mod4Y. Therefore h=+/-k mod4Y. Reduce both index congruences modulo 2Y, licensed by Y|n. Combining their independent signs gives

    i=k mod2Y  or  i+k=0 mod2Y.

Now 1<=i,k<=Y. In the first case |i-k|<2Y, so i=k. In the second case 0<i+k<=2Y, so i+k=2Y; the two upper bounds force i=k=Y. Thus i=k in every sign case.

## Edge cases checked

- **U=2.** This entails A=2,n=1 in natural Pell classification. Since 0<i<=n, i=1,Y=1,k=1. The conclusion is immediate and consistent with the general proof.
- **i=n.** The X congruence then compares with zero modulo U. The Mathlib lemma explicitly allows i<=n, so this boundary is included.
- **Y=1.** The bounds 1<=i,k<=Y force i=k=1. The final congruence argument still works modulo two.
- **h=0 or R=0.** Then R=0, and R=k mod4Y contradicts 0<k<=Y<4Y. Thus the trivial auxiliary Pell point cannot survive all equations.
- **S=0.** Impossible because B>=2 and S^2-(B^2-1)R^2=1.
- **V=0.** In the actual construction U>=2 excludes it directly: V=0 would force U^2=1.
- **Mathlib's exceptional A=2,n=1 comparison.** The lower-level equality lemma contains a collision involving index zero and index two. The public `modEq_of_xn_modEq` removes it under i>0,i<=n, precisely the hypotheses proved here; no extra exceptional case has been suppressed.
- **Negative S and R independently.** Their signs are not assumed correlated. The proof permits all four combinations and reduces only to i=+/-k mod2Y.

## Effect on the frozen compiler

For each of sixteen seed certificates, the definitions remain

    S_j=X_j+U*s_j,
    R_j=k_j+4Y_j*r_j.

Only the domain of s_j and r_j changes from natural to unrestricted integer. The new lemma proves soundness. Completeness retains the old nonnegative witnesses, so it is automatic.

Exactly 32 natural guards are removed. The three-square representation uses three integer witnesses per natural guard, so this removes exactly 96 integer variables and 32 quadratic residuals, without changing any recurrence or arithmetic wire. Applied to the independently checked 1,969-variable predecessor, the result has 1,873 variables. The final collected coefficient file must be regenerated and separately checked; this review is the unbounded mathematical justification for the domain change.

## Conclusion

No mathematical obstruction was found. The signed-index optimization follows from the pinned Pell congruence and divisibility lemmas with their actual hypotheses. This is an ordinary universal proof, not an inference from finite tests, and it is formalizable in ZFC. It does not constitute a new Lean or object-language ZFC proof certificate or independently reprove the source C222 calibration.
