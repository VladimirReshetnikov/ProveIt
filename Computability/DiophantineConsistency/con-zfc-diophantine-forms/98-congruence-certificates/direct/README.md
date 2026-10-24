# Oriented positive-power certificates and a direct consistency quartic

The main equation is a completely explicit polynomial over **nonnegative
integers**. Its lack of solutions is equivalent in ZFC to Con(ZFC), using
the stated C222/refutability calibration and Pell--Matiyasevich theorem.
This is ordinary mathematics with exact computational audits, not a new
end-to-end Lean proof or a proof of Con(ZFC).

## Deliverables

| Variant | Domain | Variables | Degree | Residuals | Expanded monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| `eq/` | Nonnegative integers | 2473 | 4 | 2089 | 20580 | 127808289 |
| `small_height/` | Nonnegative integers | 4860 | 4 | 4476 | 14719 | 1837 |
| `integer_companion.json` | All integers | 7419 | 8 | 2089 | Not expanded | Not measured |

Each equation is the sum of squares of its listed residuals. The two
quartics are also supplied completely expanded. An empty monomial-index
list denotes the constant monomial; repeated indices denote powers. All
variable orders and integer coefficients are literal data in the JSON.

The integer companion is the standard substitution
`x_i=u_i^2+v_i^2+w_i(w_i+1)` in every row. It is included to make the
integer domain fully explicit, not as a competitive low-variable result.

The previous direct quartics in the supplied incoming archive had 3614
and 6183 variables. The new 2473-variable equation reduces the former
count by 31.57%, at an increased expanded monomial count. The retained-
affine 4860-variable variant improves variables, rows, monomials and
coefficient height relative to the previous retained-affine variant.

The new primitive represents `m=n^k`, for positive `n,k`, with eleven
auxiliary natural coordinates and six equations before gate expansion.
The full ordinary proof is `ORIENTED_POWER_PROOF.md`; `direct_section.tex`
is the corresponding article section. The independently written review
and export checker are in `independent_review/`.

## Reproduce

Python 3.10+ and its standard library suffice.

    python3 verify.py

This runs the symbolic graph audit, the constructive Pell fixtures,
the positive-input induction, both independent full SOS-expansion
checks, and exact deterministic rebuild comparisons in temporary paths.
The complete consistency equation is never searched for a solution.

Individual commands, with outputs chosen explicitly:

    python3 build_equation.py --output /tmp/direct-quartic
    python3 build_equation.py --keep-linear-wires --output /tmp/direct-height
    python3 audit_oriented.py --output /tmp/direct-power-audit.json
    python3 build_integer_companion.py --output /tmp/direct-integer.json

The builder retains upstream comparison switches; only the default
positive-input construction and its retained-affine variant are the new
equations described here.

## Provenance and boundaries

The parent is `ConZFC_Shared_Certificates_2026-10-24.zip` in ProveIt's
`docs/incoming` at repository commit
`a88aefd7ddab4771534bb049c67350e397c91b9a`. Its own source snapshot is
`08200eb10fde2db408c69dffd840d6920a569b1f`. The original builder, source
proof sections, source-calculus definitions and calibration files are
included under `upstream/`; exact file hashes are in `PROVENANCE.json`.

The proof source is the numerical C222 calculus, not a K215 simulation.
It inherits the mathematical equivalences
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The primary
Mathlib Pell source is pinned at
`81a5d257c8e410db227a6665ed08f64fea08e997` (v4.32 in ProveIt's manifest).
The immediate sources are supplied. The full transitive Lean dependency
closure was not rebuilt, and no object-language ZFC proof term was emitted.

The current construction changes the positive-power graph and the sign
representation of one nonnegative CRT quotient. The Horn source, carrier,
shared CRT compiler, binomial graph and factorial graph remain inherited.
No global minimality or literature-wide novelty claim is made.

AI-assisted research for Vladimir Reshetnikov. New material uses the
repository's MIT No Attribution license. The Mathlib source retains Mario
Carneiro's copyright notice and Apache 2.0 license; see `upstream/LICENSE-mathlib`.
