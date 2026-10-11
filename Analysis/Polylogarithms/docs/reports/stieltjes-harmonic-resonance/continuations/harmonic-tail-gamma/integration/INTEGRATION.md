# Proposed ProveIt integration

Baseline: `446dca9bd65c20e409d1d2561d4ffad408103e2a`.

This is a reviewable integration proposal. No repository content was changed.
The section fragments use the prefixes `gap:`, `tel:`, `var:`, `mom:`, `res:`,
`log:`, and `audit:` so the proofs can be integrated individually. Check these
prefixes against later repository additions when choosing final canonical labels.

## Mathematical status updates

| Topic | Proposed action | Required scope |
|---|---|---|
| Optimal first-q harmonic-tail moment prefix | Add the complete `q-p=4` family to the proved cases | Positive even orders; formal coefficient rank; first new non-overlap pair `(8,12)` |
| Fixed-gap complementary determinant | Retain DPL attribution (`ar:gap-det`, `ar:gap-factor`) | It is an inherited reduction rederived here, not the new theorem |
| Pairwise ratio separation | Add the new lemma and its proof | Every pair of initial recurrence columns for each fixed gap; higher minors need a separate argument |
| Systematic rational telescoping | Mark the all-even two-tail certificate construction resolved | A supplied finite late-coordinate combination; no assumption that a particular inverse row exists |
| Gamma derivative-index-two sector | Add the finite-jet lemma, master equation, numerator theorem, and square/cube formulas | Apply the projection after canonical normal reduction; retain higher derivatives in full moment identities |
| Next two-particle resonance | Add the complete subtraction and cutoff/spectral comparison | Stated Gamma deformation, coordinate `x=N+1`, right-half-plane parameters, and overlap term |
| Higher residue spectral coefficients | Mark the normalized spatial-kernel question resolved for every fixed differential polynomial | Original origin subtraction, split at 1, complete infinity polynomial, and higher-pole corrections |
| Manuscript Family-2 example | Promote its existing conjectural display using the incoming PTI proof | Credit PTI's `bip:eq:12` through `bip:eq:21` and `bip:eq:family2-short`; this promotion is inherited |
| Gaussian S6 and current S8 | Preserve conjectural status | Do not substitute the older rejected S8 vector for the current candidate |

## Suggested locations

The harmonic-tail material naturally extends the manuscript's centered-moment
discussion, including `chapters/07-centered-trigamma-moments.tex`, after the
broader even-tail statements from the new incoming reports have been integrated.
The Gamma sector and moment-transfer material belongs with the corresponding
normal-form and finite-part theory in the incoming DPL/PTI reports. The new
resonance proof should follow DHR's first-resonance result and replace its first
proposed higher-resonance target with a theorem plus the remaining general-rank
questions. The normalized logarithmic kernels should follow DPL's residue and
spectral finite-part calculus.

For the inherited Family-2 promotion, the current canonical location is
`chapters/04-depth.tex`, label `double:eq:fam2-example`. The Gaussian material
should retain its frozen targets in the relevant depth and S8 chapters,
including `chapters/04-S8-candidate.tex`.

Update the manuscript overview, research questions, `EDITORIAL-LEDGER.md`,
`WORKLOG.md`, and `VALIDATION.md` consistently with whichever portions are
accepted. The exact computational statements can be imported from
`VERIFICATION.md`; the printed residuals must retain their diagnostic status.

## Definitions that must remain attached to their statements

- Harmonic tails are `A_r(n)=zeta(r,n+1)`. For even `r`, the polygamma factor is
  `psi^(r-1)(n+1)/(r-1)!` with positive sign.
- The tail finite part uses `n+1/2` and its nonnegative even polynomial
  subtraction. The final `(8,12)` identity is an ordinary convergent sum.
- Functional-monomial normal reduction is a linear vector-space projection;
  it is not multiplicative. Its algebraic definition is a classical input.
- The Gamma moment endpoint is the value at 1 minus the constant of its
  original-coordinate Laurent series at 0. It is not automatically zero for
  a total derivative.
- The generalized Stieltjes convention is
  `zeta(1+u,a)=1/u+sum((-1)^q gamma_q(a)u^q/q!)`.
- At the next resonance, the hard cutoff and spectral Laurent constants are
  distinct. Both the deformation and any normalization factor belong to the
  theorem data.
- The all-order Gamma coefficient theorem does not evaluate each individual
  mixed moment or prove independence of its numerical image.

## Review boundaries

The article includes its own full proofs of the new all-order claims. Classical
and repository inputs are cited explicitly. No newly false inherited theorem
was found in the targeted audit; the proposal should not be recorded as a
global repository certification or as a disproof of any unaddressed conjecture.
The complete general unequal-order rank problem and general higher-rank
resonance problem remain future research targets.
