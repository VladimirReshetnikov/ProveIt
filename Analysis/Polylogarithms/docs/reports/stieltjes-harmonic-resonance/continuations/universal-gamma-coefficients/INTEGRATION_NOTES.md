# Integration notes

## Suggested destination

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/universal-gamma-normal-forms/`

The delivery is a self-contained research report. Copying it to this destination
does not require changes to existing proofs, canonical numbering, or incoming
archive history. It does not include an automatic patch against a moving branch.

## Main proof dependency graph

1. Inherited functional-monomial decomposition (`prop:normal`) and the inherited
   finite-jet Euler principle (`lem:finitejet`). Both are reproved.
2. New universal rational kernel (`thm:kernel`), proved by `eq:telescoping`.
3. Canonical uniqueness (`lem:unique`) for every finite-jet Euler equation.
4. Complete beta coefficients (`thm:universal`), support/sign (`cor:sign`), and
   entire generators (`thm:entire`).
5. Four-variable closed coefficients (`thm:mixed`) and closed numerator formula
   (`cor:pb`) as specializations, followed by analytic applications.

For direct inclusion into the collective manuscript, prefix the local labels
(e.g. `unf:thm:kernel`) to avoid collisions with unrelated chapters. Reconcile
notation with the manuscript preamble rather than importing this report's
preamble. In particular `Nc`/`Hc` here refer to canonical normal projection and
its total-derivative compensator, not arithmetic constants.

## Exact status updates supported by this report

In the pinned `harmonic-tail-gamma/sections/08_audit_research.tex`:

- Question 5, “Determine the complete next Gamma projection”: resolved by the
  complete coefficient theorem and entire generator, including all lower mixed
  powers and all highest multiplicities. This is stronger than the requested
  `u3^2` subfamilies.
- Question 6, “Find a closed formula for the all-b sector numerators”: resolved
  by `eq:pb`, which is a finite polynomial formula uniform in b and k and makes
  numerator positivity explicit.
- More generally, further finite highest-derivative projections no longer
  require an independent recurrence: the universal coefficient theorem supplies
  every coefficient.

Do not mark the remaining numerical-image/moment problems, arbitrary unequal
harmonic-tail prefix problem, Gaussian S6, or current S8 as solved.

## Formula reconciliation

The normal form is a vector-space complement to total derivatives. It is not
multiplicative. Projection must follow normalization. The regression is:

```
sigma3(N(A6)) = u0^6 - 15*u0^2*u1^2 + u2^2
N(sigma3(A6)) = u0^6 - 15*u0^2*u1^2 - 5*u2^2
```

The complete N11 includes `11*u0*u4^2`. It must not be removed when the full
Gamma primitive is used. The new four-variable formulas describe coefficients
in full normal forms; they do not redefine the full polynomials.

The rational interpolation in k must be distinguished from the coefficient
sequence, which is zero on the forbidden parity class. Polylogarithmic series
in Section 7 start at k=1; the rational ordinary sum explicitly allows k=0 on
the even class.

## Audit and attribution

No false inherited normal-form theorem was established in this targeted audit.
The premature-truncation counterexample is a test of a known warning, not a
newly discovered error in the stated theorem. The repeated paragraph in the
inspected README is an editorial duplication only.

The pure polygamma-square subfamily, functional-monomial complement, Appell
transport, and standard Gamma/Hurwitz identities should retain prior/classical
attribution. The archive interior comparison is incomplete because the binary
members were not retrieved; do not turn the local novelty description into an
exhaustive priority claim.

## Replay artifacts

Retain both `normal_forms.py` and `universal_coefficients.py`: their algorithmic
independence is the principal finite verification feature. The JSON reports are
outputs of actual runs, not fixtures used to generate the asserted theorem.
Floating-point diagnostics are separate from exact algebra and from the
all-order proofs. The package includes no Lean formalization.
