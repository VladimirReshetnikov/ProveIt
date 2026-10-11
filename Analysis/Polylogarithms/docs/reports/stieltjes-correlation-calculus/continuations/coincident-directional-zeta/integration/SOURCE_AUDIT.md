# Audit at dcd95baeb7c0e914b138bddef6829c5b1d52b726

The repository was read only. This is a targeted mathematical audit of the
Gaussian candidates and the finite-part premises used by the new article,
not an exhaustive validation of the entire manuscript.

## Candidate status

- S2 is proved in chapters/04-S2-proof.tex.
- S4 is proved by a convergent octahedral seed plus a finite rational
  certificate in chapters/04-S4-proof.tex; the certificate uses 911
  relation rows, including 181 single-divergence regularized rows and
  17 lifted convergent distribution rows.
- S6 remains Conjecture cycloquot:conj:S6 in
  chapters/04-cyclotomic-quotients.tex. The alternative Cayley basket was
  exactly shown equivalent to this same candidate, not a new proof.
- The current S8 remains Conjecture s8new:conj:S8 in
  chapters/04-S8-candidate.tex. It is distinct from the earlier rejected
  S8 vector. Its inherited rigorous residual bound below 10^-355 is a
  proximity statement; its interval contains zero.
- The formal separating functional in the level-four quotient rules out
  a derivation of the S6 target using only the specifically restricted
  depth-one product shuffle/stuffle presentation. It does not rule out
  stronger cyclotomic or octahedral relations. No numerical relation was
  promoted to equality in this continuation.

## Existing corrections checked against current HEAD

The PSLQ wording correction proposed repeatedly in incoming reports is
**already integrated**. chapters/07-integration.tex now says to remove
known dependencies or work modulo them, require a nonzero target
coefficient, and does not require an independence theorem in advance.
Do not reapply or count that correction as new.

Three corrections/clarifications from the earlier Twisted Stieltjes
report remain relevant to current HEAD:

1. chapters/03-algebraic.tex, cleo:eq:lintanh, has log tan(theta/2)
   despite including real negative lambda in the surrounding discussion.
   It needs log|tan(theta/2)|. At lambda=-1/2, the incorrect principal-log
   RHS differs from the real integral by -i*pi^2/6.
2. The same chapter calls a special diagonal value 'non-elementary'
   without proving nonreduction to a specified algebra. Keep its exact
   value but remove this unsupported status claim.
3. chapters/07-integration.tex gives Q(sqrt(q)) as the coefficient field
   after a quadratic-character example. Scope that field to the example;
   arbitrary additive/character coordinates can require larger fields.

The supplied `carry_forward_source_corrections.patch` contains these
three narrowly scoped changes, credits this audit as a carry-forward of
prior findings, and passed `git apply --check` against the pinned commit.
It was not applied. The patch does not include the superseded PSLQ edit.

## Mathematical premises

The inspected periodic Hurwitz continuation, spectral-versus-derivative
contact law, nonlinear coordinate residue law, and unequal-grid
coincident-pair formulas have consistent local and Fourier conventions.
No new false theorem was found among these inspected premises. Their
assumptions on right-side cutoff coordinates and the smooth local
completion are necessary to the statements.

## New work relative to audited incoming questions

`sections/04_coordinates.tex` answers Q5 of Exact Identities: complete
classification of logarithmic meromorphic germs invariant under every
coordinate f(t)=t+O(t^(d+1)). The exact criterion is pole_order(a_n) <=
d*(n+1). It includes necessity, obstruction dimension, sharp Stieltjes
argument-derivative thresholds, and product consequences. This is a
proved extension of the incoming monomial thresholds; no global
historical-priority claim is made.

`sections/08b_external_audit.tex` records independently checked corrections in the
Borwein–Dilcher author PDF: H0, the B_p coefficient, and the power-series
splitting-radius qualification. The reference is the inspected PDF, not
all possible published versions.

`sections/08c_bailey_borwein_audit.tex` records further independently
checked corrections in the Bailey–Borwein author preprint of
Computation and theory of Mordell–Tornheim–Witten sums II, dated
5 May 2014, printed pages 17–19:

- Equation (84) needs signs indexed by the differentiation orders a,b,
  rather than by the summation indices n,m.
- Equation (86) is zeta^(b)(t-1) minus zeta^(b)(t), in that order.
- Equations (90) and (91) require the derivative labels (b,0,a) when
  the corresponding spectral arguments are (t,0,s).
- Equation (93) requires Gamma arguments t, rather than b; Equation
  (94) requires Gamma arguments s, rather than c.
- The direct Tornheim convergence domain requires the two pairwise
  conditions q+s>1 and r+s>1 as well as q+r+s>2. For example,
  (q,r,s)=(2,0,1) obeys the printed total-weight condition but has a
  harmonic subseries. Continuation does not restore ordinary convergence.

The article supplies corrected equations and direct derivations.
These are corrections to the inspected author PDF, with no assertion
about other versions. No external publication is modified or bundled.
