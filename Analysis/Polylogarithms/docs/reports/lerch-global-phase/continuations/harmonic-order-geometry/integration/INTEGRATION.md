# Proposed ProveIt integration

Baseline: `a0a90ef31877f98be437191c48b46f02d5456867`.
These are proposed edits, prepared for review. No remote file was changed.

## Placement and dependencies

| Contribution | Suggested placement | Dependencies |
|---|---|---|
| `sections/harmonic_order.tex` | After the harmonic Euler-sum material in chapter 04 | Harmonic generating function, gamma/beta identities; the needed variance inequality is proved locally |
| `sections/diagonal_velocities.tex` | After the elementary endpoint in `09-zero-geometry.tex` | Lerch derivative convention; elementary polynomial formula is rederived |
| `sections/diagonal_conjecture.tex` | After the diagonal theorem or in the research chapter | Exact velocity generating function; conjecture status must be retained |
| `sections/optimal_barrier.tex` | After the incoming global-phase exterior inequality | Definition of the first derivative family; the optimization proof is self-contained |
| `sections/audit_and_questions.tex` | Research/status chapter | References to the four contributions above |

The section files are reusable TeX. They use ordinary theorem, lemma,
proposition, corollary, conjecture and proof environments. Their labels
are prefixed `sorder:`, `diag:`, `diag:q:` and `opt:` to reduce collisions.
The complete preamble is in `article_template.tex`. If integrating into
the manuscript, retain or adapt these helpers:

```tex
\newcommand{\sech}{\operatorname{sech}}
\newcommand{\csch}{\operatorname{csch}}
\newcommand{\E}{\mathbb E}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\Cov}{\operatorname{Cov}}
\newcommand{\stirling}[2]{\genfrac{[}{]}{0pt}{}{#1}{#2}}
```

The diagonal family also uses `\mathscr` from mathrsfs.
Bibliography entries are in `sections/bibliography.tex`. Map incoming-report
citations to their eventual integrated locations rather than duplicating
archive references unnecessarily.

## Status changes to make

1. Mark incoming *Lerch Global Phase*, research question 2, as resolved:
   the least uniform geometric-sum cutoff is attained, while the strict
   pointwise problem has an unattained infimum at the same cutoff.
2. Replace the broad higher-branch monotonicity suggestion in
   `10-discovery.tex`. The earlier low-index counterexamples should retain
   their original attribution. Add the new infinite diagonal oscillation
   theorem and its threshold consequence.
3. Add the complete real-zero theorem for the entire order interpolation
   as a new result. Negative arguments refer to analytic continuation.
4. Keep the accessible-singularity assertion explicitly conjectural.
   Its local Puiseux identities and the conditional coefficient theorem
   do not resolve global branch accessibility.

## Statuses that remain

- The manuscript's \(S_4\) identity is already proved.
- The two \(S_6\) baskets are already known to be equivalent, but the
  reduction itself remains conjectural.
- The frozen \(S_8\) relation is already rejected by a certified interval.
  This is not a proof that its entire coordinate basket is independent.
- The strict span-unimodality conjecture from the index-three phase report
  remains open.

## Exact endpoints and conventions

- The optimal summed inequality is strict for `0 < rho <= 1`.
  At `rho = 0` the pointwise inequality has exactly two equality points.
- For positive measures, strictness can fail if the measure is supported
  entirely on the equality arguments; keep the stated domination
  hypothesis for differentiation under the integral.
- At algebraic lattice endpoints \(A>1\), velocities are nonzero by
  Hermite–Lindemann and the finite rational polynomial formula.
- The secant-number convention is
  \((\sec z)^\alpha=\sum E_{2m}(\alpha)z^{2m}/(2m)!\).
  These are positive at \(\alpha=1\); signed Euler-number conventions
  require the factor \((-1)^m\).
- Constants \(c=\pi/2\) in the harmonic proof and \(\chi=\sqrt{-2u_*}\)
  in the quantitative diagonal section have distinct notation.

## Verification artifacts

The finite rational certificates can be retained beside the corresponding
integrated sections. The numerical records and plotted curves must keep
their diagnostic labels. The code provides independent implementations,
not a completed proof-assistant formalization.

The full article includes a source audit and fourteen concrete research
questions. An import should preserve the proof-status table and the
distinctions above even if the exposition is reorganized.
