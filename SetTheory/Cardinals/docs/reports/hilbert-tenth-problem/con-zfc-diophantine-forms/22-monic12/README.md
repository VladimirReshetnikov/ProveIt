# Twelve-variable Diophantine forms of ZFC consistency

Research synthesis for ProveIt, 22 October 2026. Reviewed repository snapshot:
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

The main result is a specified polynomial `P12` in **twelve positive integer
unknowns** whose unsolvability is provably equivalent in ZFC to syntactic
`Con(ZFC)`. The report gives the complete formula, proofs, fixed-coefficient
recipe, degree certificates, and a division-free evaluator.

Read **[the report](con_zfc_synthesis.pdf)**; its editable source is
[con_zfc_synthesis.tex](con_zfc_synthesis.tex).

## Results and tradeoffs

| Construction | Unknowns | Equations | Exact degree | Arithmetic operations | Domain |
|---|---:|---:|---:|---:|---|
| Main product | **12** | 1 | 1529 | 117 | Positive integers |
| Main system | **12** | 3 | 1520 maximum | **112** | Positive integers |
| Intermediate product | 13 | 1 | **319** | 91 | Positive integers |
| Intermediate system | 13 | 4 | **288** maximum | **83** | Positive integers |
| Integer product | **26** | 1 | 2993 | 169 | Unrestricted integers |
| Integer system | **26** | 3 | 2976 maximum | **164** | Unrestricted integers |
| Retained-witness system | 16 | 7 | 24 maximum | **59** | Positive integers |

The reviewed package 09 has a 13-variable product of degree 515 at 85
operations; the new 13-variable product lowers degree to 319 at 91 operations.
The 12-variable construction saves another unknown at higher degree and cost.
The unrestricted-integer count improves the reviewed explicit 29-variable
construction. The 59-operation system improves the reviewed 60-operation
system. **No polynomial below the existing 67-operation baseline is claimed.**
These results optimize different measures; no global minimality is claimed.

An operation is a binary addition, subtraction, or multiplication, including
multiplication by a fixed numeral. Register reuse and equality comparisons are
free. System degrees are maximum residual degrees. Polynomial abbreviations
introduce no additional unknowns.

## Domains and the main idea

`P12` has exactly the positive coordinates
`J, F, alpha, z, h, i, T, s, w, eta, zeta, u`. Its unmodified formula is
**not** asserted to have the same meaning over all integers. For nonnegative
natural numbers, substitute `x+1` for every positive coordinate.

The separately proved integer formula keeps seven positive ports
`J, F, alpha, z, s, eta, zeta`, replaces each by its own disjoint copy of
`1+x^2+y^2+t(t+1)`, uses `i=2r+1` and `w=v^2`, and leaves `h,T,u`
unrestricted. This gives exactly 26 unrestricted integer unknowns.

The new elimination combines the main Pell congruence quotient with a monic
polynomial root. Algebraic integrality and a small conjugate-difference norm
force the eliminated root to be an integer. A separate Pell saturation lemma
restores the remaining rational auxiliary ordinate. These integrality proofs
exclude the extra branches that a bare resultant could otherwise introduce.

## Fixed coefficients: use one whole tuple

Every arithmetic circuit uses four **fixed** ports: `beta`, `K0`, `MC`, `MF`.
Here `beta=Bbase-1`, and the circuit's **`MF` is the shifted mask**:
the native high mask plus `Bbase-1`. It is not the unshifted native mask.
Do not splice ports from different coefficient recipes.

The new strict four-cell compiler has **5,252 tiles** and
`Bbase = 2^(5^16)`. Thus `Bbase-1` has exactly 152,587,890,625 binary digits,
a factor of 25 below the reviewed T4 recipe's `5^18` digits. These enormous
integers are specified by a terminating finite recipe and are not expanded.
The whole binding is recorded in `data/COEFFICIENT_BINDING.json`; the report proves
the compiler interface, and `code/strict_compiler.py` checks its finite data.
`code/coefficient_recipe.py --modulus 1000000007` computes the authentic four
coefficients modulo the requested integer without expanding them.

## Reproduce

From this directory, run:

```bash
python3 code/reproduce.py
make pdf
```

The required arithmetic and finite-data checks use **Python 3.10 or later and
only its standard library**. PDF compilation additionally requires pdfLaTeX
and the standard LaTeX packages listed in the source. The reproduction driver
regenerates circuit packets and check receipts; it does not expand the giant
coefficients or search for a halting K215 computation.

## What is proved and checked

The new equivalences are ordinary mathematical proofs formalizable in ZFC,
using the inherited blank-input compiler and K215 calibration. The included
checks establish algebraic identities, exact live-gate counts, degree bounds
and leading-form certificates, independent evaluator agreement, the literal
machine binding, the finite tile alphabet, and coefficient-layout conditions.

**No new Lean or Rocq formalization or fresh endpoint build is claimed.**
The inherited machine endpoint has separate formal verification records;
that status does not transfer automatically to this Diophantine bridge.
The equivalence is not a proof of ZFC consistency, and mere consistency is
not used to claim two-sided independence.

## Files and provenance

| Path | Contents |
|---|---|
| `con_zfc_synthesis.tex`, `.pdf` | Complete article and compiled report |
| `code/` | Circuit emitters, strict compiler, independent checks, reproduction driver |
| `data/` | Exact circuit packets, finite machine/tile data, and check receipts |
| `proofs/` | New derivations and independent assistant mathematical reviews |
| `reference/` | Inherited compiler/Pell interfaces and pinned comparison/verification records |
| `licenses/` | Preserved upstream licenses and attribution notices |
| `SOURCE_PROVENANCE.json` | Exact upstream paths, commit pin, source and delivered hashes |
| `data/COEFFICIENT_BINDING.json` | Whole four-port coefficient recipe and circuit binding |

The provenance file covers copied reference/data files, the sparse-polynomial
utility, the retained 60-operation baseline, and licenses/notices. All 19 copied
artifacts preserve the exact upstream bytes. New results and generated outputs
are not attributed to an upstream source file.

Suggested integration: a new `16-monic12/` directory (or the next unused
number) under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`.
Retain the existing packages for objectives they still optimize. This archive
is an integration proposal; preparing it made no changes to the repository.
