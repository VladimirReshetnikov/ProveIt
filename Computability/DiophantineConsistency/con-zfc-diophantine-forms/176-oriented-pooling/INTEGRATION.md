# Additive integration into ProveIt

## Suggested intake

Place the delivered archive at:

```text
docs/incoming/ConZFC_Oriented_Pooling_2026-10-25.zip
```

At intake, assign the next available numeric prefix under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`;
the suggested descriptive suffix is `joint-arithmetic-certificates`.
Keep this package beside the earlier proposals and preserve their
historical results and source identities. This submission does not
require an upstream write, branch change, or replacement of an existing
candidate.

Preserve the package's relative directory layout. In particular, retain
the unmodified `source/ConZFC_Pooled_Projection_2026-10-25.zip`, the literal
parent equation, and the frozen source circuits under `higher_degree/`:
the offline replay and reconstruction commands depend on them. Preserve
the supplied licenses, attribution, and proof-boundary statements.

## Suggested catalog entry

**Joint arithmetic certificates for ZFC consistency.** A direct C222
construction, with no K215 run encoding or Jones specialization, combines
Pell sign/index authentication and seventeen exact powers in one
polynomial certificate. Its explicit joint seed has 206 unrestricted
integer variables and exact degree 26. Certified monic projection gives
the following complete ordinary integer polynomials:

| Variables | Exact degree | Residuals | Live binary operations |
|---:|---:|---:|---:|
| **90** | **32,768** | 27 | 2,306 |
| **121** | **16** | 58 | 2,453 |
| **147** | **8** | 84 | 2,559 |

The full package also supplies `(194,6)`, `(135,12)`, `(115,24)`,
`(111,32)`, `(105,64)`, and `(97,256)` in
`(integer variables, exact degree)`. Every declared variable has
certified genuine polynomial dependence. The 90-variable equation is
`higher_degree/equations/integer90_degree32768.json`; its seed is
`equations/P206_joint.json`.

For each equation, the ordinary proof composed with the inherited
C222/ZF/ZFC calibration establishes in ZFC that absence of integer zeros
is equivalent to syntactic `Con(ZFC)`. All gate values in the finite
circuits are expression abbreviations, not additional quantified
variables. The largest absolute stored literal is 384; do not list this
as the expanded coefficient height. Checked height bounds are supplied,
but exact expanded coefficient maxima and support counts are not claimed.

Source 168 already suggested base weights for sign alignment, source 158
supplied same-base pooling, and source 152 supplied monic substitution.
Credit this package for the completed simultaneous signed-index/power
certificate, zero-base treatment, exact source binding, and resulting
equations. Do not attribute the earlier generic ideas to this submission.
The improvements concern the pinned direct-calculus branch, with no
global minimum or literature-wide priority claim.

## Reproduction after extraction

From the package root, with Python 3.10 or newer:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild --receipt /tmp/conzfc-intake-verification.json
```

The independent elimination checker rejects five deliberate corruptions
per final equation. Its constructor reconstructs the nine circuits byte
for byte from frozen pivots. For a focused replay:

```sh
python3 -B higher_degree/verify.py
python3 -B higher_degree/build.py --check
```

The ordinary arithmetic proofs and logical calibration remain necessary;
finite verifier success is not a substitute for them. Evaluation at a
supplied tuple uses `higher_degree/evaluate.py`. The article rebuild is:

```sh
cd report
pdflatex -no-shell-escape report.tex
pdflatex -no-shell-escape report.tex
```

## Source identity and formalization status

The comparison commit is
`315154b670d7bdb1679554734e417410c9b8187b`. The exact parent equation is
the incoming pooled-projection archive's `algebra/equation216.json`,
with SHA-256:

```text
a91308bd0c82182ea15080763cb23cb4fa0aa45a812eabb7a6cbcd21c0b95a06
```

This checksum identifies the equation file, not its containing ZIP.
The parent is a 216-variable quartic with 153 quadratic residuals.

The inherited logical declarations are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The new theorems
are presented as ordinary proofs formalizable in ZFC, with exact finite
checks and explicit source dependencies. They are not a newly compiled
end-to-end Lean/Rocq proof or an emitted object-language ZFC derivation.
Do not mark the remaining formalization obligations as closed merely
because this package's executable verifiers pass. Internal independent
reviews are AI-assisted and are not external human peer review.
