# Independent audit of the fourteen-positive carrier

## Verdict

The new adapter is mathematically sound conditional on the explicitly imported
ordinary-strong compiler, rank, signed auxiliary-index and canonical completeness
lemmas. No additional gap was found in the adapter. This is not an independent
formal verification of the whole compiler or of the ZFC calibration, and it is
not a claim of a globally smallest Diophantine equation.

The exact equation has 14 strictly positive unknowns, total degree 30 and 87 live
binary arithmetic operations. The five-equation system has maximum degree 15
and 78 shared operations. These are tradeoffs against the incoming degree52/79
fourteen-variable endpoint, not a strict improvement on both criteria.

## Mathematical checks

1. **Recovery before use of the scale.** A0=0 makes ell+r+Y/q³ a rational root
   of a monic integer polynomial t²−A. It is an integer, so q³ divides Y.
   Since q and Y are positive, s=Y/q³ is positive. X=wq was never freed.
   The scale-dependent transport and absorber bounds are only used afterward.
   The tempting two-free-scale version would not have this justification.
2. **Carrier sign and integral main root.** A1=0 makes Dstar/U an integer by
   the same monic-root argument. With q≥16, H<5a, b0>akY, and positive gamma,
   Dstar>ak(UY−5)>0. Thus the positive main Pell index is available. No
   potentially false cancellation of H modulo U is made.
3. **Absorber gcd bound.** H is odd. H≡3 mod Y implies gcd(Y,H) divides3. Every prime dividing q divides Y.
   If3 divides q, then27 divides Y and H≡3 mod27, so its3-adic valuation
   is exactly1. If3 does not divide q, gcd(qY,H)=gcd(Y,H) divides3. Therefore gcd(4qY,H)≤3, without assuming q is a
   decoded power of2. This is essential for avoiding circular reasoning.
4. **Index order.** The first recurrence gives k≡2n mod4XY², and U divides
   this modulus. Consequently 2n≡R+1 mod mu, with mu≥4q⁴/3>R+1. Since n>0,
   n≥(R+1)/2≥25. Here U=4qY≥4q⁴ after scale recovery, and
   4XY²/U=wY is an integer. P0>a+2 and c>k imply p>n, establishing the large-c rank
   hypothesis before invoking the strong-rank lemma or recovering p=R.
5. **Auxiliary sign.** As gives Q=I²>1. The auxiliary identity is exactly
   QV²−(Q−1)y²=1 for y=V+u. It excludes V=0 and y=0, and yields |y|≥|V|.
   If y<0, then u>0 forces V<y<0, contradicting that inequality. Thus y>0
   even though V itself was not assumed positive. T_old=fT>0 is legitimate.
6. **Final quotients.** After the imported auxiliary-index theorem gives p=R,
   n<R and the small representative argument give2n=R+1. Then k−2n is a
   positive multiple of both E and U. The restored gamma_old=(g−b0)/H is
   positive because g>(a+1)c and c>X. Positivity is not inferred merely from
   divisibility. These are exactly the retained absorber's estimates.
7. **Completeness.** The canonical source supplies n≥3 and k>XY. Since
   tau<ell+k and ell>k, tau−ell=(ell k+1)/(tau+ell)>k/3>s, so the supplied
   r is strictly positive. The gamma shift adds a positive integral multiple
   (k−2n)/U. The squared-modulus construction chooses a fresh auxiliary Pell
   solution; it does not assert every old T_old is divisible by f. Its
   R≡3 mod4 phase is supplied by the authentic coefficient/compiler tuple.
   On that canonical solution, V>1 and Q>1 give y²−V²=(V²−1)/(Q−1)>0,
   hence u=y−V>0. The coordinate choices do not conflict with either scale
   or the earlier gamma shift.

## Exact arithmetic audit

`check_independent.py` uses SymPy as a polynomial-arithmetic implementation;
it imports neither the author's builder nor checker. It evaluates the primary
JSON circuit exactly in the polynomial ring over Z with all14 witnesses and
four symbolic coefficient ports. The five residuals agree identically with
independently written cancellation-normal forms. Their monomial counts are
69,1157,35,408,11, and witness-weighted degrees are12,14,10,15,2.

The unique degree15 residual is auxiliary, with leading form
2w²(beta J)^5Y²(beta J−F)f⁴u.
An independent residual-symbol audit establishes that the remaining circuit
is precisely the sum of the five squares. Hence the total degree is exactly30
and its leading form is4w⁴(beta J)^10Y⁴(beta J−F)²f⁸u². This is a
universal symbolic identity and degree proof, not a finite specialization.
The actual beta is positive, so this polynomial does not vanish identically
on the fixed instance. Symbolic algebra does not extend the semantic theorem
to arbitrary choices of coefficient ports.

The degree14 main residual has two contributions to its leading form:
2U0E0c0H0R0 + H0²R0², where U0=4(beta J)Y, E0=w(beta J)Y,
c0=(eta+zeta)Y, H0=4E0, and R0=(beta J)³(beta J−F). An initial draft
omitted the second summand. The audit identified this omission and the author
corrected it; it does not change the residual or final degree.
The exact symbolic checker explicitly checks both summands.

The script also independently audits topology, unique gate names, input and
gate liveness, the87-operation count (47 multiplications,24 additions,
16 subtractions), the78-operation system, all40 pinned source files and four
compressed coefficient payloads. `RECEIPT.json` pins exactly the reviewed
proof and circuit versions. Run from any directory:

    python3 check_independent.py
    python3 -O check_independent.py

Normal and optimized (-O) runs both passed, with byte-identical receipts.

The checker requires SymPy (tested with1.14.0). The component's own replay
remains standard-library-only; this independent review adds no requirement
to that replay. Finite tests and symbolic checks do not replace the imported
unbounded number-theoretic arguments or a kernel-checked composite proof.
