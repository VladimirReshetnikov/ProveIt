# Independent proof review: unequal-scale Markov fixed-point obstruction

**PASS within the stated interface; no correction requested.** This review reads the complete frozen author note `/tmp/markov_distinct_scale_fixed_point_obstruction.md` (218 lines, 9,664 bytes), SHA-256 `4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb`, and its complete metadata JSON, SHA-256 `048c36ed52d88a27a6965e092614c0e86ae5c83898e4896df215e089feba5cb5`. No author, predecessor, supplied or frozen helper was run or imported.

The reviewed theorem forbids full actions `lambda I` and `mu [[1,-1],[0,1]]`, at distinct positive scales, on a common independent real finite-trigonometric pair f,g under continuous strictly positive normalized doubling masks. The claim concerns the whole span, not a selected counter ray or zero-test line.

## 1. Independent derivation and local cases

I independently subtracted and cross-multiplied the four operator equations, obtaining the exact identity, with `kappa=mu/(mu-lambda)`,

```
f(x)g(2x)-g(x)f(2x)
  =kappa f(2x)[f(x)-lambda f(2x)].
```

Its sign and scale are correct. Derivation requires no division by a mask difference, odd component or common coordinate factor. Equality on the circle extends to a Laurent identity without requiring finite-Fourier masks.

For `R=G/F`, rational division is permitted in `C(z)` even at points where the functions themselves vanish. If F has finite order r at z=1, then `F(z²)/F(z)` is analytic there with value `2^r`. A pole of order s>0 in R would yield a nonzero leading coefficient multiplied by `2^(-s)-1` in `R(z²)-R(z)`. This contradicts analyticity of its right side. Thus R is regular at the fixed point, and evaluation forces `lambda*2^r=1`. This handles repeated zeros and all possible common factors without assuming their cancellation preserves an invariant coordinate space.

The real eigenfunction equation and strict positivity of a at x=1/2 then imply `f_o=O(x^(r+1))`. The bounded mask difference cannot satisfy `(b-a)f_o=(mu-lambda)f(2x)`, whose right side has nonzero order-r coefficient. This includes r=0. The proof never assumes zero mean, even masks or harmless cancellation of a shared factor.

## 2. Smooth corollary and equal-scale dependency

The smooth corollary's Taylor split also passes: order(g)<r gives incompatible leading orders; order(g)>=r, including equality and flat g, forces `lambda 2^r=1` and the same positivity contradiction. Its conclusion is only that a smooth escape requires f flat at x=0.

For the equal-scale corollary, the full 114-line `markov_doubling_mixed_subspace_boundary.md` was reread, SHA-256 `baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063`. Its shared nonconstant finite eigenfunction has a nonzero odd component with finitely many circle zeros, so the same-eigenvalue equations force the continuous masks to agree. Eigenvalue one is separately excluded for an independent two-dimensional identity space by the positive-averaging maximum principle and dense dyadic preimages. These are the exact hypotheses required by the present corollary.

The retained identity-only `I/3` example checks directly and does not contradict the pair prohibition.

## 3. Scope and provenance limits

The other two provenance hashes authenticate: `markov_distinct_scale_fourier_boundary.md` has SHA `23e5c13ca92ce1522489c6a54a6905f184daf0023d0a39ef421bd14f911941ee`; `markov_distinct_scale_first_profile_exclusion.md` has SHA `33231c7f6306a5ad2c6b64a1bf809a2ccee08f7e87274e285ff93ca62d3b8850`. Their proofs were not newly reread in this review and are not premises of the fixed-point argument. No finite experiment or earlier degree census is used to support its all-degree conclusion.

The result leaves arbitrary continuous coordinates, smooth flat common eigenvectors, vanishing masks, unnormalized operators, changing charts and restricted-line actions outside scope. It yields no integer compiler, paid gate saving or global arithmetic lower bound. I do not newly audit the separate dilation-three construction here.

The companion reviewer JSON records exact byte bindings and read coverage. Only fresh byte-reading metadata code was used. No source array was evaluated, no numerical search or external literature certification was performed, and no repository/Git mutation occurred.
