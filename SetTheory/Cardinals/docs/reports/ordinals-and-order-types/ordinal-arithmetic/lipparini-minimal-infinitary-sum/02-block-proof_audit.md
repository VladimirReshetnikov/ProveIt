# Proof audit and review guide

This document records the structure of the proposed proof. It is not an
independent referee report, a formal certificate, or a guarantee of correctness.
The authoritative mathematical statements and proofs are in article.tex/pdf.

## External dependency

Lipparini, arXiv:2505.00424v2, Definition 3.1 and Theorem 3.4:

1. The operation S has the displayed three-case evaluation in the manuscript.
2. S is weakly monotone and is least among weakly monotone operations strictly
   increasing at z-special increases.
3. Every e-special admissible F therefore satisfies F >= S.

The final implication is proved in the manuscript from the definitions of the
epsilon and zeta thresholds. The new proof does not purport to replace the
published proof of Theorem 3.4. All additional ordinal manipulations used here
are elementary Cantor-normal-form calculations or are proved in the article.

## Candidate and terminology

Write e for the least ordinal with finitely many entries >= e. This threshold
is positive and is unchanged by finitely many coordinate modifications.
A nonzero limit lambda is called corrected when its final Cantor exponent is a
successor. This is a local term introduced for the proof, not a claim of standard
terminology. Such lambda has countable cofinality, even when it is uncountable.

For e = lambda+n in a corrected block, the candidate is

    (lambda natural-product omega) # R # (omega*n + c),

where R is the finite natural sum of differences from lambda of entries
>= lambda+omega, and c is the finite sum of t-n+1 over entries lambda+t >= e
below lambda+omega. The # signs mean natural addition.

## Upper-bound / admissibility obligations

- At a fixed threshold, a subthreshold coordinate contributes zero. The
  exceptional-coordinate contribution is positive at the threshold and strictly
  increasing thereafter. Thus coordinatewise monotonicity and the exact
  equality criterion hold.
- At a structural uncorrected source threshold, the candidate equals S and S
  is e-strict for single-coordinate changes at that threshold. One such change
  and weak monotonicity of S handle a larger target threshold.
- This argument must NOT be applied merely because candidate = S accidentally
  at the bottom of a corrected block with no near exceptions.
- Within a corrected block, increasing the threshold from lambda+n to lambda+m
  gives omega*n+c < omega*m+c', and the far contribution cannot decrease.
- For a target threshold >= lambda+omega, use u=lambda+n+1 and the coordinate
  interpolation gamma_i=max(alpha_i,min(beta_i,u)). It has threshold u+1,
  the same far coordinates as alpha, and its S-value strictly exceeds the
  candidate value at alpha. Monotonicity of S gives the remaining upper bound.

These arguments establish admissibility without assuming minimality.

## Lower-bound / minimality obligations

Take an arbitrary admissible F; assume no permutation or zero-insertion
invariance for F.

- Outside corrected blocks, F >= S is already the desired bound.
- At e=lambda, replace every near exceptional entry lambda+t by zero, use
  F>=S, and restore it in t+1 e-special strict steps.
- At e=lambda+n, n>=1, first remove every far finite part and replace every
  near exceptional entry by lambda+n-1. These are finite coordinate changes,
  so the threshold stays fixed.
- If R0 is the new far contribution, H=(lambda natural-product omega)#R0
  has zero finite part. The target lower bound before restoration is H#omega*n.
- For n=1, keep k copies of lambda, use other copies of lambda to realize a
  cofinal sequence below lambda, and preserve far entries. Apply the n=0
  bound to get H+k; take the supremum over finite k.
- For n>1, keep k copies of lambda+n-1 and cap every other non-far entry at
  lambda+n-2. Apply the induction hypothesis one level below and take the
  supremum over finite k.
- Finally restore the removed far finite parts and the near exceptional
  entries. Each restoration step reaches the unchanged threshold or higher,
  so each forces a strict successor increase of F.

The restoration is essential: ordinary addition of omega would erase the
finite parts of the far contribution. Suprema alone do not give the full bound.

## Consequences checked in the article

- Exact equality criterion on coordinatewise comparable sequences.
- Permutation and zero-insertion invariance, derived for the candidate after
  minimality, rather than assumed for arbitrary competitors F.
- Finite-support agreement with finite natural sum.
- Constant-sequence formula and the distinction between successor and limit
  *exponents*.
- Correction only at Cantor exponents 0 or 1.
- Cardinality preservation, with finite support and infinite support separated.
- A set-like well-founded rank characterization. The rank proof does not imply
  well-foundedness of unrestricted strict coordinatewise comparison.
- A finite multiset model with independently computed bounded ranks.

## Specific counterchecks

- At a corrected limit threshold the summand is `1 + d_e(a)`, not `d_e(a) + 1`.
  For infinite d_e(a), the former equals d_e(a).
- For one omega^2+5 and an otherwise constant-omega sequence, the answer is
  omega^2*2 + omega + 5. The +5 must survive.
- At a threshold with a limit final exponent, the original S formula is
  unchanged; the positive exceptional contribution need not be one.
- Exceptional coordinates are counted with multiplicity.
- A successor threshold b+1 is not the same as the repeated background b.
- Taking suprema of finite-capacity ranks does not recover every unrestricted
  multiset rank. This is explicitly explained, not used as a proof shortcut.

## Verification scope

Python tests use exact finite Cantor normal forms below epsilon_0. They compare
three evaluation paths sharing one arithmetic backend. Finite multiset ranks
are separately computed from the order relation. Tests do not certify arbitrary
ordinal exponents, infinite sequences, the external theorem, or the transfinite
minimality proof. No Lean/Isabelle/Coq certificate or external human review is
included. The complete English proof is the substantive evidence for the claim.
