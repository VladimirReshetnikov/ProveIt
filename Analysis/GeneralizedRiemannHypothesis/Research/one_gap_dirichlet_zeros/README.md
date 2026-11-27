# Recovering all Dirichlet zeros from one zero-free interval

Read **one_gap.pdf** for the mathematical statements, proofs, source analysis and examples. **one_gap.tex** is its complete LaTeX source. The abstract inverse theorem covers any locally finite positive real divisor with a summable inverse-square tail. The application to primitive Dirichlet characters uses the critical-line conclusion of Dirichlet GRH. The arithmetic examples concern the Riemann completion.

## Reproduce the calculations

Run from the extracted directory with Python 3.9 or later. Leave Python assertions enabled.

| Command | What it checks |
| --- | --- |
| `python3 examples/xi_certificate.py` | Uses interval arithmetic on Riemann's theta integral to locate the observations of orders 9 and 11 and certify the first ordinate and its multiplicity. Python standard library. |
| `python3 examples/xi_certificate.py --high` | Certifies 14.1347251417337 < γ₁ < 14.1347251417510 from orders 65 and 67. Python standard library. |
| `python3 examples/resonance_check.py` | Uses integer sign tests and rational bisection on the four-pole example exhibiting cancellation. Python standard library. |
| `python3 examples/xi_demo.py` | Evaluates both zeta examples numerically with mpmath 1.3.0. It repeats the Cauchy integration at different precisions, radii and node counts. |

Recorded output is next to each program. The first floating-point experiment supplies no zero location. The second supplies the first positive ordinate and removes its simple pair before estimating the second ordinate. The entire-spectrum reconstruction is an exact-data theorem. Section 4 quantifies its sensitivity to measurement errors.

## Compile the paper

A standard TeX Live system with Latin Modern and AMS packages can build the single source. Run `pdflatex one_gap.tex` twice. No external bibliography or graphics are required.

## Verification scope

The new theorems are proved in the paper. The Python scripts check specific examples. For the cited upstream Lean development, the paper links the inspected revision and the independent machine verification. The new inverse theorems are presented as research results with a targeted prior-work comparison. The paper identifies the nearest published results found in that search.
