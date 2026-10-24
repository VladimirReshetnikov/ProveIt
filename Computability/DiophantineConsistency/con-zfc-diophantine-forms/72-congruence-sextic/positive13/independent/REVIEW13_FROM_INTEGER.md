# Independent internal review of the thirteen-positive degree-28 equation

Reviewed `pell_research/section13.tex`, `PROOF13.md`, and the frozen literal
`p13_degree28.json`; no primary file was modified. The circuit SHA-256 is
`1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49`.
The remaining reviewed hashes and finite diagnostics are recorded in
`REVIEW13_DIAGNOSTICS.json`. This is an independent AI-assisted internal
review, not external peer review or a proof-assistant certificate.

## Conclusion

The displayed equations, denominator clearing, degree certificate, and
soundness/completeness argument agree with the frozen circuit. I found no
mathematical defect in the new reduction. Its proof remains conditional on
the explicitly named inherited native/Pell/calibration results, in the same
sense as the original source packages. The finite checks do not prove those
unbounded results or supply an internal object-language ZFC derivation.

## Fixed data and operation convention

The four native ports are the entire compact source44 tuple, with
`beta=2^590069-1` and the already shifted high mask. The six derived leaves
are exactly `B=beta+1`, `b=3beta`, `b2=b^2`, `L=beta*b2`,
`Kfinal=b2*L^2`, and `four_beta=4beta`. They are fixed integers, not extra
witnesses or independent parameters. In particular `L=beta*b^2` makes
`Vhat=L*V` exactly, and the constant subtracted in Aa is `b^2*L^2`.

All thirteen witness variables are strictly positive; interpreting this as
an unrestricted-integer equation would invalidate the argument. The DAG
has 98 live binary gates: 25 additions, 16 subtractions, 57 multiplications.
The four-residual system costs 91 gates, and the final sum of squares adds
four squarings and three additions. Multiplication by a fixed scalar and
squaring each cost one gate. Fixed-leaf creation and reuse are excluded.
This convention agrees with the repository comparison but is not bit
complexity or a count of expanded coefficients.

For the final archive, attach a concrete path/hash map to the complete
source44 payloads: the circuit's `coefficient_binding` currently names
that tuple in prose. The parent contribution already supplies the payloads,
but a standalone deliverable should make their binding unambiguous.

## Proof order checked

1. The strong equation first forces `Nf/b` integral. Positivity of Nf
   holds without knowing the native congruence. Thus `q=B+3beta*j`, and
   `q>0` excludes negative j. This restores integral positive J, q>=B,
   q=2 mod3, and integral R before source bounds or main-carrier recovery.
2. Supplying F,alpha,C positively makes the packing bounds independent
   of transport sign. The first carrier recovers both `q^3|Y` and
   `q-1|Bt`; its root may be signed, as the proof permits.
3. Main-root positivity follows before quotient recovery. Here `H<5a`
   follows from `Y>=q^3`, and `MY>5` is immediate. No assumption q|X
   is used in this bound.
4. The normalized strong equation supplies the precise signed auxiliary
   theorem hypotheses: c=psi_A(p), f=chi_A(m), c|m, m>2p,
   Maux=Delta*I>=2, c|Maux, Maux^2=Delta(f^2-1), and 0<p,R<c/2.
   Both auxiliary Pell coordinates are nonzero. The modular conditions
   V=-c mod f and V=-R mod c follow exactly. Package61's
   `positive/SIGNED_INDEX_LEMMA.md`, section 3, permits either sign of V
   and y, so taking y=|V+u| afterward is legitimate. The proof does not
   silently use the different ordinary-strong large-c lemma.
5. The modulus estimate `gcd(4qY,H)<=3` uses both q coprime to H and H
   odd. The inequalities yield mu>q^4>R+1. Divisibility of 4XY^2 by
   M=4q^2Y follows from q^3|Y and does not require q|X. Therefore exact
   index recovery precedes recovery of q|X, h, and gamma_old.
6. Transport is restored with the original z_old rather than an
   unjustified positive shifted quotient. Its numerator is positive even
   when z_old-1=0; this is the improvement enabled by the positive C
   coordinate. K0>=0 would already suffice, because w,C>0.
7. Completeness supplies f0=f-j>0, r>0, and gamma>0 by the displayed
   bounds. Fresh T,u come from the inherited odd-index squared-modulus
   reconstruction. The argument does not assume an arbitrary old
   auxiliary quotient is divisible by f.

## Degree and transcription

The fixed clearing identities for As, A1, and Aa are exact. The strong
residual has leading form `-9beta^2*i^2*(eta+zeta)^4*X^2*Y^6`, degree 14.
The other residuals have degree at most 13. Therefore the coefficient
`81beta^4` of `i^4*eta^8*X^4*Y^12` proves exact degree 28 on the authentic
coefficient slice. No unproved claim that symbolic generic degree survives
specialization is needed.

As supplementary transcription diagnostics, I independently evaluated the
four displayed residual formulas against the frozen DAG on 32 assignments,
using the actual compact coefficient numerals reduced modulo 2^127-1.
They and the output sum of squares agree. I also independently counted and
checked liveness of every gate. These are diagnostics; the symbolic checker
and written proofs carry the exact and unbounded claims respectively.

## Requested small presentation fixes

- In the final cancellation display, `\widehat Y^{,2}` and
  `\widehat V^{,2}` contain a literal comma in the exponent. Replace with
  `\widehat Y^{\,2}` and `\widehat V^{\,2}`, or simply squared symbols.
- Add one explicit sentence giving the six precomputed fixed leaves and
  the operation convention above; the current description is correct but
  terse about why fixed `4beta` and `b^2L^2` do not add gates.

These presentation points do not alter the equation or its proof.
