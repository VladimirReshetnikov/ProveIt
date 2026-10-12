# Independent analytic audit of the marked-gap contribution

Audited files: `research_identities/contribution.tex` and `notes.md`.
Baseline commit: `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

## Verdict

No blocking mathematical error was found. Bare interpolation, finite
decoration closure, local gap insertion, set-partition inversion, and
independent differentiation form a valid proof chain. The result gives an
individual ordered cluster for identical marked pairs, and the fully
symmetric sum for unequal marks. The article states this limitation
correctly. No edits were made during this independent audit.

## Published interpolation input

I independently opened Ihara--Nakamura--Yamamoto, *Interpolant of truncated
multiple zeta functions*, Ramanujan Journal 67, article 1 (2025), DOI
https://doi.org/10.1007/s11139-025-01045-2 .

Corollary 4.2 gives holomorphy on C^d times (C minus the real ray at most
-1). Their Z_w uses positive summation indices, whereas the present Z_c
uses nonnegative indices, so the correspondence is w=c-1. Proposition
5.3 gives Phi_c=Z_c^{-1}*Z_1. Thus
Phi_a*(Phi_b)^{-1}=Z_a^{-1}*Z_b in the correct convolution order. At each
fixed word, convolution and inversion use finite polynomial operations.
This proves joint spectral entireness on the stated right-half-plane
endpoint domain. It is not a claim of entire dependence on endpoints.
Theorem 5.2 supplies the bare harmonic-product character law.

## Finite decorations

The one-tail proof in its initial absolute-convergence domain needs only
pointwise products of the other letters, not bare-power letters. It
therefore applies with arbitrary other finite decorations. The induction
parameter is the number of interior Q factors: insertion may increase
word length but removes the chosen Q factor. The shift law first removes
all shifted Q factors. The algorithm terminates in bare relative words
at affine sums of arguments with entire endpoint coefficients.

Every step agrees with the independently defined convergent quotient on
a nonempty open domain. The identity theorem proves the continuation and
its independence of elimination order. No interpolation from integer
endpoint differences occurs. Derivative decorations can explicitly be
handled by assigning independent parameters to their Q factors before
differentiating and only then identifying parameters.

## Local partition formula and its meaning

The three-series expression for E[P] is correct: its a,a terms combine
into the weak opposite ordering. It is independent of the separated
representation of P. In particular the higher-depth word is not used to
define E. Adjacent one-tail formulas, together with the shift law, prove
the gap insertion identity with arbitrary remaining boundary
decorations.

The gap-splitting identity is an exact identity of primitive functions in
independent right-half-plane variables. Unused gap factors are expanded
as boundary decorations before each insertion. The new label is inserted
in every strict slot or merged with one existing block, generating every
ordered set partition exactly once. Möbius inversion gives the classical
coefficients. Independent derivative orders add inside each block
without multinomial factors. Identical marked pairs make all k!
permutation terms equal and yield the stated elementary/Bell polynomial.

The reduction is to decorated double quotients and explicit ordinary
double sums with specified continuation. It is not a theorem reducing
all values to endpoint constants or establishing minimal arithmetic
depth. The notes' phrase “not concealing a new higher-depth zeta
coordinate” should be replaced by the narrower assertion that the
ordinary-series definition is independent of the identity being proved.

## Multigap clarification recommended

For general decorated lattice letters, absolutely convergent Z_c is a
quasi-shuffle character under pointwise multiplication. Characters into a
commutative function algebra form a group under convolution; hence the
relative quotient is also a character. Continuation preserves the law.
Stating this explicitly avoids attributing a decorated-letter theorem
directly to INY.

The top gap follows from the first-position one-tail formula and the
shift law. The interior gap follows by subtracting successive-position
formulas. The bottom gap follows by subtracting the last-position
one-tail formula from the singleton stuffle formula, using
H(u)=Q(u,b)-Q(u,a). The multigap result follows gap by gap.

The notes' displayed ordered chain of complex variables should be
rephrased as an indexed list of independent right-half-plane variables.
The TeX contribution already uses the latter formulation.

## Explicit checks by derivation

The Gamma-square identity, its factor 1/2, and its absolutely convergent
domain Re(s),Re(t)>3 are correct. The log-Gamma difference uses analytic
branches on the right half-plane. Differentiating
partial_x zeta(u,x)=-1-u Q(u+1,x) gives
partial_x zeta^[j](0,x)=(-1)^j j gamma_(j-1)(x), and hence the displayed
normalized primitives. The half-order pair has the correct merged
-gamma_2(z+1)+gamma_2(y) contribution. The unequal 0,1 pair has the
correct minus sign on the Gamma--gamma_1 product and evaluates only the
symmetric sum. Independent derivatives followed by specialization are
correctly distinguished from a total derivative along the diagonal.

The formal verification program replays an analytically proved
one-tail identity; it is not an independent proof of that identity. The
article correctly treats numerical checks as diagnostics.

## Baseline correction status

No actual mathematical error requiring correction was found in the
baseline rank and harmonic-gap material examined in this work. The
baseline correctly withheld the several-marker claim; its single-marker
theorem needs no correction.

The rank formula's lower-binomial-index restriction is already explicit
in `canonical-digamma-fifth/sections/07_tail_rank.tex`, lines 135--137:
the lower index must be at least 2, and a spurious lower index 0 changes
the formula. Incoming Quartic Spectral Reconstruction repeats it in
`sections/03_eventual_rank.tex`, lines 28--29; incoming Alternating
Tails explicitly inherits it in `sections/07_rank_refinement.tex`,
line 48. Preserve this normalization without presenting it as a new
correction. The order-ten completion resolves a remaining case; it does
not correct a false source theorem.
