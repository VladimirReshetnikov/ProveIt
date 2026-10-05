# Independent review of the mixed-coordinate doubling obstruction

**PASS.** The new result excludes a common nonzero scale identity/decrement pair on every finite trigonometric coordinate space, rather than excluding only two individual sine frequencies. It correctly permits a two-dimensional identity block by itself. It gives no arithmetic-operation saving or general obstruction to Markov computation.

Root read the complete frozen author note (114 lines), SHA-256 `baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063`, and the complete inherited `markov_sine_lift.md` (192 lines), SHA-256 `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2`. The pure-harmonic predecessor and matrix-lift note were authenticated; their earlier reviewed content is context, not a new full review of their original report sources. No supplied or frozen program, saved array, or numerical source evaluation was executed.

## 1. Independent mathematical challenge

For a normalized doubling mask, write its two branch weights as `(1+b(x))/2` and `(1-b(x))/2`. Applied to a function f at the point2x, this weighted average equals its half-period even part plus b times its odd part. Thus two masks with the same eigenfunction and eigenvalue have difference annihilating the odd part pointwise.

The odd part of a nonconstant finite trigonometric eigenfunction at nonzero eigenvalue cannot vanish identically. Otherwise the support is even and the transfer operation divides its largest absolute frequency by two, in conflict with the unchanged support of a nonzero scalar multiple. A nonzero finite Laurent polynomial has finitely many zeros on the circle. The mask difference consequently vanishes on their complement and, by continuity, everywhere. This proves uniqueness without division at those exceptional zeros and without a finite Fourier requirement on the masks.

A possible constant shared eigenvector deserves separate treatment. Every normalized operator fixes constants, so this case requires eigenvalue1. Strict positivity then makes a maximum propagate to both preimages, and by iteration to each dyadic inverse grid. Their density proves that every continuous real fixed function is constant. The same conclusion holds for complex functions by real and imaginary parts. A two-dimensional identity block at eigenvalue1 is therefore impossible.

For any other nonzero scale, an eigenvector of the proposed nonidentity matrix at eigenvalue1 corresponds to a nonconstant common eigenfunction. The uniqueness argument makes the two masks identical, so their restrictions coincide and the second matrix must equal the identity. This proves the general matrix statement, including the decrement shear and any real change of coordinate basis.

The inherited dilation-three construction supplies the other direction of the minimum-dilation claim. Its displayed sine masks have coefficients `[2,0;0,1]/5` and `[2,-1;0,1]/5` in the triangular Fourier layout, yielding precisely I/5 and D/5. Their polynomial numerators are `(4t^2-1)^2+2` and `(4t^2-1)^2+2(1-t)`; the latter is positive on[-1,1], by the two intervals split at3/4. The new note explicitly restricts the integer dilation class to b>=2. Nothing here proves a global minimum denominator.

## 2. Retained boundary examples

**Review remark 1.** The stronger identity-only exclusion would be false. For `a=1+(2/3)cos(theta)`, the transfer sends sine to one third sine, and cosine to `(1+cos(theta))/3`. Since constants are fixed, it sends `cos(theta)-1/2` to one third of that same function. These two functions are linearly independent, and the mask is at least1/3. The author retains this explicit counterexample in numbered Remark1 rather than overstating the family theorem.

**Review remark 2.** Different scale factors are not covered by shared-eigenpair uniqueness: the masks with cosine coefficients2/3 and1/2 send the same sine to eigenvalues1/3 and1/4. The author's Remark2 correctly preserves this boundary. Neither changing scale with the action, requiring identity only on a zero-counter line, nor choosing nontrigonometric coordinate functions is refuted.

## 3. Accepted scope

All conclusions follow from the displayed elementary identities and unrestricted proofs. No numerical experiment or new helper is needed for them. The provenance binding authenticates the frozen notes but is not a replacement for those proofs. The result does not compile selected words, integer normalizations, ordinary input, branch guards or unbounded computation histories. The universal84/187/18 construction is unchanged.
