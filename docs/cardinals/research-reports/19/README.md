# Fixed tail parameters and stationary collapse

Research continuation of the reports and Lean reference files supplied in
`Cardinals3.zip`, prepared for Vladimir Reshetnikov, 18 September 2026.

## Contents

- `Fixed_Tail_Parameters.pdf`: the 20-page report, with detailed English proofs.
- `Fixed_Tail_Parameters.tex`: the complete, self-contained LaTeX source.
- `README.md`: this file and build instructions.

The source uses the supplied report's `newpxtext`/`newpxmath` typography,
Forest/Olive/Muted/Sage/Pale palette, page geometry, theorem styling, headers,
and colored assessment boxes. Font files are not included.

## Main result

Let lambda be ultraexacting and theta its successor cardinal in the ambient
universe V. The report constructs an invariant bijection b: lambda -> V_lambda
and lambda many tail classes q_i, with pairwise disjoint cofinal representatives.
For every finite set F of indices, let N_F = HOD_(b, q_F), where the entries of
q_F are allowed as whole set parameters, not as freely chosen representatives.

Theorem 1.2 proves that N_F regards lambda as inaccessible and theta as
measurable. The ambient nonstationary ideal, restricted to N_F's subsets of the
ambient countable-cofinality set at theta, belongs to N_F and has an atomic
quotient with fewer than a single critical point kappa many atoms.

One club in V works simultaneously for every finite F: its points of ambient
cofinality omega are inaccessible in all the N_F. Each N_F computes lambda's
successor strictly below theta and has its own countable-cofinality stationary
set at theta destroyed in V. Any set forcing representing V as an extension of
N_F must fail the theta chain condition in N_F and have ambient size at least
theta (Theorem 9.2).

Theorem 10.2 combines this result with the published ultraexacting/I0 calibration
and coding theorem. The resulting simultaneous package is equiconsistent with
ZFC + I0, even with V_lambda contained in ordinary HOD, no exacting cardinal
below lambda, and the bijection b omitted from the parameters defining the
inner models.

## Status and limits

This is a conventional, unrefereed mathematical argument, not a Lean-checked
proof. No compilation of the supplied Lean project was performed. The report
identifies the established literature results it uses and does not claim that
the ordinary-HOD strong-measurability theorem or the ultraexacting/I0 calibration
is new. Its continuation is the finite-tail-parameter strengthening, common
club, and associated successor and ground obstructions. Priority is not claimed.

There is no claimed unconditional inconsistency of ultraexacting cardinals or
I0. The measures live on the inner models' power sets, not the ambient power
set. The theorem does not assert that these inner models are distinct or that
any is a forcing ground. It does not cover arbitrary infinite tuples of tail
parameters. Both the internal/external distinctions and the dependence on
published consistency inputs are discussed in the report.

## Build

Use a current TeX Live or MiKTeX installation providing the packages named in
the preamble, including `newpx`, `tcolorbox`, `microtype`, and `xurl`.
No external bibliography database, images, or shell-escape commands are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Fixed_Tail_Parameters.tex
```

Alternatively, run `pdflatex` three times to resolve references and the contents.

The supplied PDF was compiled with pdfLaTeX, checked for unresolved references
and overfull boxes, rendered for visual inspection, and checked for text outside
the physical page boundaries. These typesetting checks are not mathematical
formal verification.
