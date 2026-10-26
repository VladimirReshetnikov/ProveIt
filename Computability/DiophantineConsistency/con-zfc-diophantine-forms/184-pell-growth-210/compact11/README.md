# Constant dilation and an integral inverse Lucas polynomial

This compact companion supplies one explicit polynomial in **eleven strictly
positive integer unknowns**, of **exact degree 174**, evaluated by **104 live
binary arithmetic operations**. Composing the new proof with the retained
ordinary native/compiler/refutation calibration gives

    ZFC proves: (P has no strictly positive integer zero) iff Con(ZFC).

The finite tuple of coefficients is entirely specified: the four compressed
integers, their exact reconstruction program, the printed finite recipe and
all raw/compressed hashes are present. The largest coefficient has 592884
bits. No coefficient is an unspecified program index or existential parameter.
The JSON is the literal polynomial definition; its registers are abbreviations,
not extra quantified unknowns. No recurrence or variable exponent occurs in it.

## What changed

The new application replaces a variable Pell dilation with the fixed integer
210. This clears denominators in a third-order inverse Lucas expansion before
modular reduction, retaining a fourth-order rank congruence at much smaller
polynomial degree. A separate positive projector quotient, enforced by an
integer unit product, prevents the denominator collision that invalidates the
tempting ten-variable shortcut. The proof also supplies a new early size
bound and a cofinal strong-Pell-seed completeness argument.

The inspected source-115 equation has eleven positive unknowns, degree 211
and 107 operations. Its coefficient bit lengths agree with this equation,
but its whole-tuple K0 is different. This is a domain-and-size comparison,
not a same-polynomial contraction. Source172 has ten positive unknowns,
degree 214 and 87 operations, and uses the same whole coefficient tuple.
It remains preferable on variable count and operation count. No global
minimum or historical priority over the broader literature is asserted.

The ancestry of this compact equation still includes the native K215
calibration. It is a separate tradeoff from the companion direct quartic.

## Read and reproduce

- `PROOF_constant_dilation.md` gives both unbounded mathematical directions,
  all new inequalities, exact degree and the rejected shortcut.
- `section_constant_dilation.tex` is a complete include-ready LaTeX section
  for the accompanying report.
- `constant_dilation11.json` is the 104-operation literal graph. Its eleven
  variables are J,F,alpha,i,T,w,s,n,eta,zeta,kappa; s denotes Y in the proof.
- `build_constant_dilation.py` deterministically emits that graph; `--check`
  checks byte equality without changing it.
- `verify_constant_dilation.py` independently checks every gate against the
  displayed formula by exact polynomial cuts, proves the inverse identity
  in Q[m,x]/(x^4), recomputes the complete highest homogeneous part, and
  reconstructs all four fixed coefficient payloads.
- `INDEPENDENT_REVIEW.md` records the separately assigned mathematical audit.
- `PROVENANCE.json` identifies the exact repository snapshots, archive bytes
  and original member paths of all retained dependencies.
- `SHA256SUMS` binds every delivered file except itself.

From this directory, using Python 3 and only its standard library:

```sh
sha256sum -c SHA256SUMS
python3 -B build_constant_dilation.py --check
python3 -B verify_constant_dilation.py --mutations
python3 -O -B verify_constant_dilation.py --mutations
```

Both modes accept the same certificates. The 208 single-operator mutations
are all rejected. Neither verifier searches for a zero or runs the encoded
machine. A nonzero literal coefficient proving attained degree is

    [J^49 w^25 s^57 i^10 eta^32 kappa] P = 192 * 210^37 * beta^49 > 0.

The complete leading homogeneous form has 300 monomials. In particular,
the degree claim includes the outer unit product and the projector factor.

## Retained proof closure and its boundary

`source140/` is the complete byte-for-byte compact subtree of the pinned
Centered Residues archive. It contains all fixed coefficient bytes,
`rebuild_coefficients.py`, licenses and notices, and the ordinary proof
sources used here. In particular:

- `proof_sources/universal_pell.tex` supplies signed folding, normalized
  strong rank, universal projection and the explicitly stated inherited
  native/compiler/refutation theorem.
- `proof_sources/uniform_ratio.md` proves the ratio bound uniformly for
  every positive dilation, including 210.
- `proof_sources/scaled_native.md` and `proof_sources/indexed_native.md`
  provide the source reconstruction and whole-tuple BFS943 conjugacy.
- `proof_sources/indexed_constants.tex` prints the full finite coefficient
  recipe, including the 436-character seed and tile enumeration.

`TRACE_PROOF.md` is the exact source163 trace-radical proof. `source172/`
retains the directly inspected parent proof and equation, with exact source
metadata in `SOURCE172_FILES.json`. `171-positive.json` supplies the
unchanged whole-tuple coefficient binding used by the new builder.
`comparison115/` retains the exact comparison graph and binding; its K0
differs as stated above. Historical scripts inside retained source folders
are archival dependencies, not additional advertised entry points.

The unbounded conclusion uses the named ordinary native/compiler/refutation
calibration; this package does not independently re-prove its machine-to-ZFC
calibration, supply a new object-language ZFC derivation, or give an end-to-end
proof-assistant kernel certificate. The finite checks verify the emitted
algebra and fixed data, and are not a substitute for that ordinary proof.
The independent audit is an AI-assisted mathematical review, not external
human refereeing. No assumption that ZFC is consistent is used by either
existential direction.

The original licenses and notices remain intact. New material follows the
included MIT No Attribution license, matching the retained component.
