# Final mathematical and editorial review

Reviewed `report.tex` in `output/ConZFC_Carriers_and_Even_Indices_2026-10-24`
without editing it. Primary scope: Sections 1--9, with detailed independent
comparison of the twelve-integer formulas, proof order, height argument,
completeness map, attained coefficients and division-free norm appendix
against the previously audited literal circuits.

## Outcome

No mathematical defect or artifact mismatch was found in the weak-carrier
or mixed-modulus construction. The stated degrees 768,784,800,816,1040 and
operation counts 161,154,147,144,140 agree with the independently checked
circuits. The two displayed principal equations have exactly the audited
center shifts and radicand scales. Their coefficient monomials and powers
of 2,3,beta agree with the independent every-gate calculations.

The following possible failure points were specifically checked:

* beta's residue is 1 modulo 3 because 1064921 is odd. Consequently the
  asserted q and X residues, H/Delta residues, and first-radicand residue
  are correct.
* Y=qv admits v=0 initially; the explicit Delta=H=3 branch makes all
  unconditional claims valid. It is excluded only after the carrier
  recovers v=q^2(2u+1).
* S=0 excludes s=0 and r=0 without assuming c!=0. Rational root extraction
  precedes the strict guard; that guard excludes c=0 before the Q>1
  auxiliary descent. The main rank and native bounds are used only after
  the cubic source scale is recovered.
* The prime-adic carrier lemma uses M^5, not merely M, to recover M|z.
  The remaining H congruence is explicitly only a fifth-power congruence;
  no false cancellation of repeated prime factors of H is used.
* gcd(H,M)=1 follows uniformly from H=3 modulo q, 3 not dividing q, and
  H odd. No coprimality of H and the strong witness I is assumed.
* The height proof is valid with the actual coefficient tuple. At the
  boundary r0=24, the final exponent comparison has a strict margin 15.
  The proof does not silently replace the actual beta by the generic x>=64
  assumptions of earlier results.
* Completeness uses kappa=Kstar/H+(v-q^2)/M, fixes I before requesting a
  residue, and uses the exact quotient A/S=c^2 H^4 pi(T+kappa)/I. The
  rational and integral choices of n have the correct inverse shifts.
* The appendix's cleared norm formula and both canceled q0 expressions
  agree exactly with the independent free-ring identities.
* The text does not claim consistency, a global optimum, a new end-to-end
  proof-assistant theorem, or literature-wide priority. It identifies the
  inherited native/direct calibration as a separate mathematical theorem.

## One requested clarification

At the start of Section 9, explicitly include k>=1 among the front
hypotheses (in addition to m>=0 and n>=1). The later proof uses K=2k>=2,
including in the orientation argument excluding m^2 n^(2k)=1. This is
consistent with the positive-power call contract, but should be visible
in the report rather than left implicit. No other correction was needed
within the primary review scope.

For Section 9 I also checked the abscissa-residue proof, independent sign
cases, the |Y|=1 parity obstruction, the exact-index argument, base-one
qualification, and two-step identity at the mathematical level. Full
source-row binding and the 566-variable construction remain covered by
the separately assigned direct-compiler reviewer and its literal checks.
