# Independent mathematical review: positive-eleven degree 211

**Conclusion: PASS**, relative to the explicitly inherited ordinary native,
Pell and finite-refutation calibration. No sign-circularity, lost canonical
witness or additional source-interface assumption was found. This is internal
AI-assisted mathematical review, not external peer review or a kernel proof.

Reviewed component: `positive11_doublecenter`, with final choice
`T_old=T+F+alpha`, `L=k*T_old`, and strong-root center `Cf=(a+2)I`.
The literal circuit SHA256 is
`b482a1e952536c445918dd5a9e03fdaea0081e0e016e6a1bcbf7be9a26b5a92d`.

## Soundness and dependency order

1. The finalizer gives N8=A1=0 since both residuals are squares modulo four.
   Radical separation requires only positive inputs and T_old>0. The norm
   supplies rational signed roots; integer-square reasoning and the
   adjacent-coefficient Pell descent make all three integral.
2. Therefore M divides Zbar, giving q^3|Y and q-1|Bt without any sign of Bt.
   The rational root Dstar/U of the integer 1+Delta*c^2 is integral.
   Main Pell classification gives p>=2 since c>=3. First Pell index m1=1
   would force k=2, eta=zeta=1 and c=2Y+1, contrary to
   c>=2(a+2)>=4Y+4. Hence m1>=2 and

       c>kY>=4(2XY^2+1)Y>8XY^3>=8q^9.

   This entire bound is established before C>0.
3. For h=F+alpha>=2, the unconditional fixed-mask bound gives
   |R|<q^3(q+h)<q^4*h<c*h. Consequently

       c*T<c*T_old-R<c*(T+2h),
       1<V<Df*c*(T+2h).

4. Let u=y-V for the positive auxiliary root. The exact identities and
   elementary bounds

       delta-(Delta-1)Df=Delta(I^2-1)>0,
       c<k(Y+1),   Delta-1>2(Y+1)

   give

       0<u<V/delta<c(T+2h)/(Delta-1)
          <k(T+2h)/2<k(T+h)=L.

   Also Cf^2-Df=I^2-1>0 gives Cf>f. Thus L+Cf+V>f+y.
5. If Bt/(q-1)<=0, the new signed-root transport equality has right side
   strictly larger than the sum of the absolute root values. This is
   impossible. Thus Bt>0 and then C>0. The recovered source witnesses
   u=|y_signed|-V and r=n+L+V+Cf-f_signed-y_signed are positive. Signed
   f_signed,y_signed must remain signed in r. All other source equations,
   including A1, are unchanged.

## Canonical completeness

The inherited auxiliary reconstruction gives positive integral T_old and
Vstar,y_star from Maux=Delta I. Since R>=7 and I>=c^2,

    Vstar>=Maux^6,    f^2<Maux^2,
    T_old>Maux^4/c>=c^7>q>F+alpha.

Thus T=T_old-F-alpha>0. Also

    Maux^4/c=Delta^4 I*(I^3/c)>(a+2)I=Cf,

so L=k*T_old>Cf and L>k. The canonical weighted gap satisfies

    r=W*t0+tau-ell-k-s>qW-2k>2L

because t0>=q, s<k, tau>ell, q>=16 and L>k. Hence

    n=r-L-Cf+f+(y_star-Vstar)>0.

The new Zbar is exactly M(tau+f+y_star). The canonical adaptive-main
gamma is unchanged and positive.

## Source-interface pin and scope

The retained `upstream/70-residue-orientation__eleven__PROOF.md`, Section 1,
pinned to repository commit `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`,
explicitly permits **every positive weight** in soundness and weights
`hstar>=k`, chosen **after** the strong/auxiliary roots, in canonical
completeness. L meets both conditions. The retained source61
`SIGNED_INDEX_LEMMA.md`, Sections 4--5, supplies normalized strong-rank and
positive auxiliary reconstruction with c|I; I=i*c^2 meets that hypothesis.
No deleted denominator-support factor is needed because the independent
adjacent-coefficient descent supplies rational-root integrality.

The degree audit separately confirms the universal 30-term center and
229-term norm, weighted degrees 63 and 126, and polynomial denominator
clearing to degrees 99 and 198. The nonzero coefficient
`2^13*(3*beta)^48` at the specified degree-211 monomial proves exactness.
The literal graph contains 112 binary operations. These finite checks
support the stated algebra; they do not replace the inherited unbounded
calibration theorem.

Minor wording correction: the first paragraph of PROOF.md says the old
degree-257 equation has "the same 114-operation cost". Since the final new
cost is 112, replace that phrase with "degree 257 and cost 114 operations".
