# Independent mathematical review of the Diophantine chapter

**Status:** Manual mathematical audit completed; no substantive flaw found. This is not a Lean kernel check or a verification of object-language iPRA derivations.

**Reviewed file:** `chapters/diophantine.tex`  
**SHA-256 at report preparation:** `53d6801929a6a50fb56eabffa0a6fa3c6eec3c209110490a2a44985e0b53020b`

## Scope

The audit covered rational normalization and the rational-root argument; primitive Pythagorean triples; both finite descents; continuant determinant, growth, and error identities; Farey separation; finite rational and simultaneous Dirichlet approximation; the transfer with explicit slack to represented reals; and all Pell results. Particular attention was given to nonzero/positive side conditions, explicit clocks, and the distinction between bounded witnesses and unrestricted least-counterexample arguments.

## Finite descents

For square area, the four factors m, n, m+n, m-n are pairwise coprime because the Pythagorean parameters are coprime and have opposite parity. The resulting w and z are odd. The equation w²-z²=2v² forces v even; the constructed triangle has integral legs, square area (v/2)², and hypotenuse u with u²=m<c. Normalization before the transformation cannot increase the previous hypotenuse, so strict decrease holds for the entire totalized transformation.

For the quartic descent, normalization divides z by the square of gcd(x,y). In the first parametrization, m must be odd and n even. Coprimality of m and 2n therefore permits m=u² and n=2v². The second parametrization gives coprime r,s with rs=v², hence r=A²,s=B² and A⁴+B⁴=u². The new hypotenuse is strictly smaller. Both fuel arguments use a decidable tuple invariant and terminate after at most the original hypotenuse, so no unrestricted least-counterexample induction is hidden.

## Pell approximation and existence

For B=4(D+1), Q=B(Y+1), C=4D+2, the integer-square-root approximation A/Q² satisfies all stated rational inequalities. Rational Dirichlet approximation yields a positive p and a nonzero integral norm of magnitude below C. If q were at most Y, the two displayed error contributions are each strictly below 1/2, contradicting the nonzero integral norm. Thus the lower denominator bound is justified without a real floor.

The recurrence T₀=0, Tᵢ₊₁=B(Tᵢ+1) gives Tᵢ+1≤(B+1)ⁱ. In particular qᵢ<U for U=(B+1)^(K+1), including the last index i=K. The norm tag and the two residues fit within K=2C³ classes. A collision makes both displayed quotients integral even for negative norm. The identities comparing their numerator squares prove that both numerator signs equal the common norm's sign; hence x,y are positive. The norm is exactly one, x≥2, and the stated H bound dominates both coordinates.

## Fundamental powers

The existence box permits a globally minimal positive second coordinate: a competitor with smaller y would also have smaller x. Multiplication by the conjugate fundamental unit gives x'>0, y'≥0, and y'<y by the three explicit difference-of-squares identities. A clock of the original y therefore suffices. The invariant reconstructs the original pair from the current pair and the recorded power, while strict growth of second coordinates proves uniqueness.

## Remaining formalization work

The paper's mathematical arguments survived this audit. Actual Lean semantic proofs, quoted primitive recursive definitions, and checked derivations in the chosen iPRA calculus remain separate implementation obligations. The audit does not promote the supplied Lean outline to a completed formalization.
