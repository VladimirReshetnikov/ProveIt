# Root review and the independent-scale minimum-dilation corollary

**PASS.** Root read the entire 218-line author proof, SHA-256 `4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb`, and its metadata receipt `048c36ed52d88a27a6965e092614c0e86ae5c83898e4896df215e089feba5cb5`. Root independently derived the determinant identity and checked the fixed-point pole calculation, Taylor cancellation, positivity contradiction and smooth finite-order consequence. This is a mathematical proof review, not a numerical or formal proof certificate.

With delta=mu−lambda and kappa=mu/delta, eliminating the bounded mask difference gives `F_o G2−G_o F2=kappa F2 F_o`. The identity-mask equations give `F−lambda F2=(2−a)F_o` and its G counterpart. Cross-multiplication therefore gives

    F G2−G F2=kappa F2(F−lambda F2).

No division by an odd part or coordinate factor is used in this derivation. Passing to rational functions is legitimate even when F vanishes on the circle. At z=1 its finite order r makes F(z²)/F(z) regular with value 2^r. A pole of G/F cannot cancel under z↦z² because 2^(−s)−1 is nonzero. Evaluating the now regular identity forces lambda=2^(−r).

In the real coordinate, the normalized eigenfunction equation then implies `a(x+1/2)[f(x+1/2)−f(x)]=O(x^(r+1))`. Positivity at 1/2 and continuity allow division by a locally bounded-away-from-zero coefficient. Thus f_o is O(x^(r+1)), contradicting `(b−a)f_o=delta f(2x)`, whose right side has nonzero order-r coefficient. This includes r=0, repeated roots and arbitrary common factors. Continuity of the masks suffices; their Fourier expansions are not assumed finite.

The separate smooth corollary is also sound. Its direct Taylor comparison includes g of lower order than f, equal or higher finite order, and g flat at zero. It rules out finite vanishing order for the common eigenvector f; it does not exclude smooth encodings with f flat at zero. The unequal-scale proof does not depend on the preceding Fourier-degree or first-profile classification.

## A sharp consequence with independently chosen scales

Among allowed integer dilations b>=2, the minimum dilation for this full identity/decrement pair on a real two-dimensional finite-trigonometric coordinate space is **three, even when the two positive scales can be chosen independently**.

The all-scale doubling exclusion supplies the lower bound. For the upper bound, root read the complete 192-line `markov_sine_lift.md`, SHA-256 `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2`, as mathematical text. On the basis `(sin(theta),sin(2theta))`, its dilation-three masks are

    a_I=1+[4cos(2theta)+2cos(4theta)]/5,
    a_D=1+[4cos(2theta)−2cos(theta)+2cos(4theta)]/5.

Their nonconstant Fourier frequencies are not multiples of three, giving normalization. The exact sine coefficient formula `a_(3k−m)−a_(3k+m)` gives I/5 and D/5. Frequencies outside the two-sine span cannot occur, and oddness excludes a constant component. For t=cos(theta), the respective numerators are

    (4t²−1)²+2,
    (4t²−1)²+2(1−t).

The first is positive. The second is at least 1/2 for t<=3/4, and at least 25/16 for t>=3/4. Hence the masks are strictly positive. Equal scales are permitted in the independently chosen-scale class, so this proves attainment at b=3.

This is a minimum **dilation**, not a minimum arithmetic cost, denominator, witness count or polynomial degree. It does not turn the two counter-coordinate actions into a complete guarded universal program. The original q=5 denominator minimum is restricted to its own even-mask standard-sine encoding and is not extended here.

The equal-scale half was checked against the complete pinned `markov_doubling_mixed_subspace_boundary.md`: its uniqueness lemma handles nonconstant finite eigenfunctions and its positive averaging argument handles eigenvalue one. The identity-only I/3 example remains valid. No earlier theorem is refuted; previously open unequal-scale profiles are now settled negatively within their exact full-action interface. Nonnegative masks with zeros, restricted-line actions and nonanalytic coordinate functions remain separate questions, subject to the stated smooth-flat necessary condition where applicable.

No supplied, archived, frozen or predecessor helper, builder or source array was executed or imported. No numerical search was used. The arithmetic frontier remains 84 operations.
