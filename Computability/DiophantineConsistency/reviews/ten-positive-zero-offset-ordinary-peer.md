# Ordinary peer: remove the scaled-base offset

**PASS.** I independently read the full soundness and fresh completeness
argument, checking the cited universal P4 bounds, original ratio/projection
lemmas, SOURCE61 auxiliary-completeness lemma and original fresh unscaled
restoration. The final research and candidate proofs are byte-identical,
SHA256 `8555e4f3cb78aba44e091e35d61b08a26f63f638b60d3d1795d3395680eff6f9`.
No circular use of a new zero or an old scaled witness was found.
The intended99-operation graph and its full coefficient/count verification
are separate author/root scope; this note reviews the ordinary reduction.

The semantic change is A=mu*a+1 with a=Y*(X+1), replacing mu*(a+2)+1.
The further identity mu*(XY+Y)=(mu*Y)*(X+1) is an exact free-ring
factorization of that same new parameter, with no additional semantic
change. It licenses sharing an existing muY register regardless of any
Pell, domain or fixed coefficient assumption.

## Soundness hypotheses survive in the required order

The replacement ratio inequality follows directly from the universal P4
bounds. I independently collected the exact lower-base difference

    (2*lambda*a+1)^2*X-(X+1)^2*(4*X*lambda^2*Y^2+2)
       =4*lambda*a*X+X-2*(X+1)^2
       >=2*X^2+X-2>0.

For the upper bound A<=lambda*(a+1) and the strictly larger denominator
2P-1>4*X*lambda^2*Y^2 give the claimed factor(1+1/a)^(2r).
Thus this is a proved replacement for the old offset-specific ratio
family, rather than an application of that statement at an inadmissible
parameter. Its upper bound is stronger than the previously used3/a bound.

The new A still satisfies A>4,A>Y,A-1>mu*X*Y,Delta>V0+1 and H>3a.
All three radicands remain positive before extraction. A=1 modulo mu
preserves the weighted noncancellation proof before parity or integrality.
Main folding is uniform in A and uses c<=I,c^2 dividing I and its exact
auxiliary congruence; it requires no deleted constant offset. First-index
exclusion remains valid since2Y+1<2A, giving the same late c bound and
positive Kpos. The weighted transport proof is therefore licensed at the
same stage as before, with a still rational rho.

The mask/rank arguments recover p=R before q parity. Only afterwards is
mu^2 coprimality used; H=-1 modulo mu preserves that license. The first
norm comparison is strengthened: P-A=mu*Y*(2*mu*X*Y-X-1)>0. The new
ratio lower bound then gives X^(r+1)<3a<H. The whole-product projection
uses the same universal H=4A-5 identity and the odd-H cancellation of2,
without cancelling q^3(q-1) or a separate factor modulo each prime.
The old strict product bound still forces X=2^R.

After the divisibilities and half-quotient rounding have been recovered,
the source restoration constructs fresh **unscaled** witnesses at a+2.
It is explicitly independent of the present scaled A. The retained
unscaled ratio and auxiliary lemmas still apply to these fresh values;
the proof never divides the present I by mu or identifies two different
scaled kernels or native K0 coefficients. Positive J=1 soundness remains
the previously reviewed source-theorem case.

## Fresh canonical completeness closes every new witness

Keep the refutation's canonical J,F,alpha,w,Y,R,X and transport quotient.
Here Y is the inherited integer half quotient M/2 in the binomial-ratio
argument, with X=2^R and R=3 modulo4. The newly proved ratio bound gives
Y<c/k<Y+1 for c=psi_A(R),k=2*psi_P(r+1). This establishes eta=c-kY and
zeta=k-eta positive before assuming any candidate zero. The literal first
norm is then exact. Its base-one congruence gives mu^2 dividing
e=k-R-1, and its positive excess gives rho>=1.

The new strong ordinate I=psi_A(Rc) is an integer multiple of c^2:
put D=chi_A(R); composition gives I=c*psi_D(c), and the binomial
composition congruence modulo D^2-1=Delta*c^2 gives c dividing psi_D(c).
Thus i=I/c^2>=1 is a new valid positive coordinate. No old i is reused.

The cited auxiliary-completeness lemma is uniform in A. With
S=Delta*I and r=(R-1)/2 odd, it supplies
V*=Q_r(S^2),y*=psi_S(R) and
T*=(V*+c+R*f^2)/(c*f^2), with exact integer quotients and y*>V*>0.
Its hypotheses c=psi_A(R),c dividing I and the strong norm all hold at
the newly constructed values. The required offset T=T*-alpha is also
strictly positive, not merely an invocation of T*>0. Indeed c<I<S,
f^2<S^2, and

    V*>S^(2r),
    T*>V*/(c*f^2)>S^(2r-3)>alpha.

The actual canonical r>=48 and A>q>alpha license this inequality. The
small-index auxiliary lemma by itself would not imply T*>alpha; the
growth bound is used at the correct stronger canonical hypotheses.

The fresh ratio interval and k>=4P give c>2X directly, so Kpos>0 without
appealing circularly to soundness of a zero not yet built. The universal
projection at X=2^R gives integral kappa=Kpos/H. Since
Kpos=H*X*c-2*Kold and Kold>0, kappa<Xc. On the other side
f>(A-1)I>=mu*a*c^2>Xc. Finally tau>k>Y>=s and the displayed sum
n=W*t+rho+3*tau+f+(y-V)-s-kappa is a positive integer even when the
transport quotient t is0. All its terms are now licensed. The normalized
center becomes3*tau+f+y and an all-positive weighted factor vanishes.
This completes a fresh witness construction, without a positive pointwise
old/new inverse or an unstated cofinality assumption.

## Independent diagnostics and scope

The accompanying helper imports only the earlier independent polynomial
collector. It checks both complete free-ring identities,192 exact rational
ratio comparisons,108 changed parameter bounds,140 post-parity coprimality
cases and an odd-q counterexample to premature coprimality. Nine toy
half-quotient intervals and four small-index strong/auxiliary constructions
check the universal formulas. They are explicitly not complete calibrated
source tuples and are not used instead of the unbounded argument above.
Normal and optimized modes both pass and pin the exact final proof bytes.

The leading scaled parameter retains its degree5 form after subtracting
the lower-degree2 term2mu. The universal centered norm and unchanged
unique leading-register forms give the inherited scalar degree368 leading
component. Binding that calculation, the99 live operations and all four
coherent fixed payloads to the literal graph is separate author/root
verification scope. No candidate, common document, page or Lean file was
edited by this peer; no Lean or historical emitter was invoked.
