# Ordinary peer: fixed root weight and unshifted strong ordinate

**PASS.** I independently read the complete ordinary proof of
`candidates/ten-positive-weighted-roots`, including its inherited chronology
and both existential witness maps. Its final proof SHA256 is
`92d260efefbda2fd5a0fceda7a093b6175c6876ef9385afc74a5484e335123d1`.
I found no use of parity, root integrality or the deleted lower-bound shift
before it has been proved. This peer covers ordinary correctness; the reported
102-operation literal and degree368 are separately checked by the author and
root, not attested by this note.

The replacement is I=i*c^2 and the weighted signed roots (3*tau,f,y).
Before interpreting any Pell index, the positive integer squares obtained
after multiplication by sqrt(delta) are congruent to (-9,-1,-1) modulo
mu=q^2+1. A zero pair involving 3*tau forces mu to divide8. The other zero
pair would give the equality of an integer V^2-Df with -1/Delta, impossible
since Delta>1. Thus it does not rely on f or y already being rational.
The complete zero-center norm is2025=3^4*5^2; a zero triple therefore forces
mu to divide2025. The elementary square residues modulo3 show gcd(mu,3)=1
for odd and even q alike, hence mu would divide25 although mu>=1025.
This proves all required signed noncancellation before the signed-sum
character argument extracts the rational roots. No selected prime divisor,
superincreasing hypothesis or parity shortcut is used.

The retained strong folding uses I>=c and c^2 dividing I, both supplied by
I=i*c^2. It gives c=psi_A(p) with odd p. First-index exclusion then gives
c>8*X*mu^2*Y^2>8*mu. Consequently
4*tau<8*X*mu^2*Y*c<mu*X*Y*c^2<(A-1)*I, while f<A*I. These inequalities
imply 3*tau+f<(2*A-1)*I<H*I, since A>4 and H=4*A-5. This restores exactly
the weighted transport bound after folding, without claiming that the input
i itself is at least mu. The rational rho and negative-Bt contradiction
then follow in the same pre-parity order as in the accepted102/388 parent.

Once positive transport gives the mask and rank bounds, p=R precedes q
parity. Odd R excludes odd q, so only then is the old coprimality used.
Multiplying the integral signed-root relation by3 changes neither its
denominator nor the whole-product projection. The source61 restoration
constructs fresh unscaled strong coordinates; it does not require dividing
the present I by mu or a pointwise positive inverse for the new i.

Completeness keeps all canonical old102/388 data except
i_new=i_old+q^2 and n_new=n_old+2*tau. The first equality preserves the
old strong ordinate I, hence every radicand, transport coefficient and
projection term. The second shifts the center from tau+f+y to3*tau+f+y
and is strictly positive. This supplies an explicit new zero; soundness
returns a refutation and then the canonical old witnesses, so a bijection
of arbitrary zero sets is neither asserted nor needed.

The separate JSON authenticates the reviewed proof and inherited ordinary
sources. Independent integer diagnostics check the modulus obstruction for
993 q values including odd q, the exact norm2025 and45 weighted hierarchy
instances. They are implementation diagnostics; the preceding arithmetic
arguments are unbounded. No candidate, page, common document, Lean file or
historical emitter was changed or executed.

The final prose refresh changed only the grammatical phrase “coefficient3 do not”
to “coefficient3 does not”. Reversing exactly that substitution reconstructs
the previously reviewed proof hash `a5ed9f73b36b6d0e80767e6d13c82c5ee6957d67f85748ac3b89ef99893f0491`; no formula changed.
