# Proof and novelty ledger

## Published mathematical inputs

**Counting bridge.** Dai–Hou–Liu–Thawinrak–Wang, Theorem 1.2, identifies a Hall-demand support enumerator with the augmented bipartite root polytope's Ehrhart numerator. Davis–Kohl, Theorem 3.10, states the Ohsugi–Tsuchiya identification of that numerator with the perfectly matchable set polynomial. Demand coordinates in the first source use the opposite shore convention; swapping shores is an integral coordinate permutation of the augmented root model.

**Concavity.** Röhrle–Ulirsch, Theorem A, already proves binomially normalized log-concavity for regular-minor counts of bimatroids. A generic bipartite matrix has a nonzero minor exactly on matchable supports. Brändén–Huh supplies the Lorentzian basis-polynomial and nonnegative substitution/derivative theorems. The graph inequality is an application of this published theory, not a newly discovered bimatroid result.

**Intersection realization.** The construction is the realizable case of Röhrle–Ulirsch, Theorem E. The article includes its coordinate-projection proof and all normalization factors.

**Sampling and approximation.** The chain and its interpretation are explicit here; the spectral-gap and general FPRAS machinery are due to Anari–Liu–Oveis Gharan–Vinzant. No new general matroid mixing theorem is claimed.

**Exact hardness.** Counting transversal matroid bases is #P-complete by Colbourn–Provan–Vertigan. The leaf transform and exact interpolation transfer this hardness to the quantities in this article.

## Repository inputs re-proved rather than trusted blindly

The predecessor's Part IV contains the balanced transitivity/palindromicity criterion and transport gamma formula. The article re-proves both by directed-path cancellation and a reachability count. Its extension to every bipartite graph uses the separately proved extremal-support factorization.

The predecessor's Part II contains the height-two transform. The article gives its zero/positive-coordinate partition argument before using it for exact-counting hardness.

The predecessor credits Shivam Patel for the eight-element nonreal-root example. This package retains that credit and treats the example only as a separation between real-rootedness and ultra-log-concavity. Its discriminant and transformed coefficients are checked independently.

## Elementary arguments proved in the article

- A bijection from matchable supports to bases of a fundamental transversal matroid; importantly, this is not a demand-vector bijection.
- Generic nonvanishing of every structurally nonzero minor.
- Refinement of total demand/support equinumeracy to an identity by exact receiver support, using subset inversion.
- The factorial calculation giving the sharp normalized coefficient inequality once the Lorentzian theorem is imported.
- Top-support Cartesian factorization and the lower bound `(a-r+1)(b-r+1)`.
- Complete palindromic-core classification, including isolated vertices and deficient matching rank.
- A finite convex-order proof and the exact positive-weight star classification for equality in the variance bound.
- Independence oracle, activity conventions, conditioning by matroid minors, and detailed balance of the support chain.
- A polynomial sample/error allocation for the counting self-reduction.
- Leaf-extension identities and polynomial-time Turing reductions for exact graph and height-two preorder counting.

## Scope of the research claim

The article answers the unimodality and palindromicity components of the specified bipartite support-enumerator problem, and develops all-preorder ULC and its explicit consequences. These are applications and extensions relative to the pinned ProveIt report. No comprehensive global-priority claim is made. The strongest imported general theorems retain their original attribution.

Still open here: the full real-rooted graph class; flag realizability; a direct demand/support bijection; and the more ambitious questions listed at the end of the article. Nothing depends on solving those remaining questions.

## Verification boundary

No Lean, Rocq, or other proof-assistant build was performed. The exact Python checks cover finite instances and cannot replace the written all-size arguments or the cited general theorems. The sampler is a reference implementation, not a production FPRAS. The random tests check exact arithmetic inequalities on seeded cases, not asymptotic mixing from observed frequencies.

The full regression suite passed. The separate certificate confirms discriminant −5243 and two real roots for the monic quartic in the nonreal-root example. The PDF was compiled with pdfLaTeX and visually checked after cross-references stabilized.
