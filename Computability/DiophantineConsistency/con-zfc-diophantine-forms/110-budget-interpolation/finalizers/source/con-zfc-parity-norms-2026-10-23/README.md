# Parity norms for a smaller ZFC consistency equation

**Primary result: 13 unrestricted integer variables, exact total degree 1,392,
211 live binary arithmetic operations.**

The proposed equation is the single integer polynomial `parity13_shifted_dag.json`.
The human-readable definition and ordinary mathematical proof are in
[`report/parity-norms.pdf`](report/parity-norms.pdf) and its standalone LaTeX source,
[`report/parity-norms.tex`](report/parity-norms.tex).

Composed with the retained ProveIt native/Pell/refutation theorem, the new
arithmetic reduction proves, by ordinary mathematics formalizable in ZFC,

\[
\mathrm{ZFC}\vdash
\bigl(\neg\exists\mathbf x\in\mathbb Z^{13}\;P_{13}(\mathbf x)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

This proves an equivalence. It does not prove either consistency or inconsistency.

## What changes mathematically

1. **Fixed parity weights combine squares.** A rational signed sum of roots with
   weights `1, 2, 4, ...` forces every radicand to be a square when all but the last
   unweighted radicand are odd. In each nontrivial squareclass, the least power of
   two has an odd coefficient and cannot cancel. This works before positivity is
   known, including negative and zero inputs.
2. **One norm also carries the main Pell congruence.** Its center contains the
   required residue modulo `H`. A vanishing norm recovers the old quotient
   integrally, eliminating its separate existential coordinate.
3. **A polynomial coordinate shear lowers the degree.** Pairing the final root
   signs exposes `L^2-d4 = 64 H^2 V^2 + 256 H^2 (Q-1)`. Translating the norm
   coordinate by `4(2Q-1)V` lowers exact degree from 1,888 to 1,392.
4. **A compact exact norm evaluator lowers circuit size.** The generic five-root
   norm uses 99 binary operations. With the complete native registers, the main
   polynomial uses 51 additions, 31 subtractions and 129 multiplications.

The method does not use the Jones or Sun universal-polynomial compressor. This
particular instantiation retains the existing K215-based coefficient tuple and
its native semantic calibration. The square-combination lemma is more general.

## Measured equations

All rows below use unrestricted integer variables. Arithmetic counts charge
every live binary addition, subtraction and multiplication, including squaring
and multiplication by fixed constants. Shared values and literal leaves are
free; the six large fixed constants are separately disclosed.

| File | Variables | Exact degree | Binary operations |
|---|---:|---:|---:|
| `parity13_shifted_dag.json` | **13** | **1,392** | **211** |
| `parity13_direct_dag.json` | 13 | 1,888 | 205 |
| `parity14_unit_product_dag.json` | 14 | 862 | 150 |
| `parity15_unit_product_dag.json` | 15 | 204 | 128 |
| `centered16_sos_dag.json` | 16 | 120 | 123 |

Additional variants and their measured counts are retained in
`COMPACT_METRICS.json`. The placed source-67 thirteen-integer comparison has
degree 10,461,744 and 519 operations: the primary row reduces degree by about
7,516 times and operations by 59.3%. This is a measured comparison at thirteen
integer variables, not a claim of global optimality. The repository already has
constructions with fewer variables.

## Exact specification and coefficient data

`parity13_shifted.json` supplies the ordered polynomial abbreviations and
factorized residual specification. `parity13_shifted_dag.json` supplies the
literal topologically ordered arithmetic program. Every gate is `add`, `sub`, or
`mul`; there are no radical, division, exponentiation, oracle or variable-exponent
gates. The norm notation in the proof abbreviates an ordinary integer polynomial.
Neither intermediate registers nor fixed coefficient ports are extra unknowns.

The thirteen independent coordinates are
`j, C_native, z, h, r, v_scale, w3, T, c0, pair_root, p1, p2, t_parity`.
All range independently over **Z**. No additional inequality or congruence is
part of the final equation.

The six fixed integers are in `coefficients/payloads/`, bound by their bit lengths,
raw and compressed hashes in `coefficients/BINDING.json`. Together they occupy
615,883 uncompressed bytes. The source-34 finite generator and literal machine
and tile tables are in `coefficients/source34/`. Running
`python3 coefficients/verify.py` reconstructs and compares the exact bytes. This
does not run the machine to halting or test consistency. In this tuple `MF` is
already `MF_native + beta`; do not shift it again.

## Reproduce the result

Requirements: Python 3.10 or later, standard library only. LaTeX is needed only
to rebuild the PDF. No network access or proof assistant is required for the
supplied arithmetic verification.

```sh
python3 verify_release.py
```

This checks the release manifest when present, creates a temporary work copy,
reconstructs the coefficient tuple, rebuilds all new equation packets and compact
programs, and runs the algebraic, degree and independent audits. It checks that
all regenerated specifications are byte-identical to the distributed versions.
It leaves the distribution unchanged. The included `RELEASE_VERIFICATION.json`
records a successful run from the final package location.

To retain a new run's receipt:

```sh
python3 verify_release.py --output /path/to/verification.json
```

To rebuild the report:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error parity-norms.tex
```

### What the checks establish

- Exact coefficient-by-coefficient equality for all 495 terms of the generic
  four-root norm and all 20,349 terms of the generic five-root norm.
- Independent exact equality between the compact 99-operation norm and the
  formal multiquadratic norm, without importing the source builder.
- Literal DAG input census, syntax, topological order, liveness and operation
  counts for ten concrete compact polynomials.
- Exact degree upper bounds and attainment on explicit univariate
  specializations using the authentic fixed coefficient bytes. The main degree
  1,392 coefficient is `756708762 mod 1000000007`, hence nonzero. A separate
  finite-difference calculation agrees.
- Retained parent rows and reconstruction maps, together with finite adversarial
  diagnostics and negative controls. The diagnostics are supplementary checks;
  the report supplies the unbounded proof.

Independent checkers were also run under `python3 -O`. The finite inherited
coefficient recipe should be run in ordinary Python mode because it retains
assertions from its source.

## Proof status and scope

The report proves the new parity, root-integrality, congruence-recovery,
normalization, completeness and degree arguments. Completeness is an
**existential reconstruction from canonical native witnesses**; it is not a
claim that every old solution already has the new normalized multiplier.

The native compiler and its relation to formal ZFC refutations remain inherited
ordinary mathematical theorems. The full parent package and its proofs are
retained at `upstream/pell-congruences-source/`. This contribution does **not**
claim a newly completed end-to-end Lean, Rocq or encoded-ZFC certificate.
Finite tests cannot establish that semantic theorem or consistency.

The research did not locate this parity construction in the inspected repository
or incoming packages. No worldwide novelty or absolute minimality claim is made.
Unimplemented smaller-weight and shifted fourteen-variable ideas appear only as
future directions in the independent reviews. They are excluded from the
released primary polynomial and its measurements.

## Archive map and provenance

- `report/`: the main standalone paper, LaTeX and PDF.
- `*_dag.json`: literal compact arithmetic programs; `abstract_norm5_dag.json`
  is the generic 99-operation norm.
- `parity*.json`, `centered*.json`: readable polynomial packets and exact degree
  certificates.
- `build.py`, `build_norm_family.py`, `compact_norm.py`: reproducible builders.
- `audit*.py`, `independent_*.py`: algebraic and independent checkers.
- `*_AUDIT.json`, `*_METRICS.json`, `results.json`: checked receipts.
- `PROOF.md`, `PROOF15.md`, `independent_proof_audit.md` and `*_REVIEW.md`:
  derivations and independent mathematical reviews.
- `coefficients/`: complete literal coefficient data and finite reconstruction.
- `parent/degree88_17.json`: exact incoming seventeen-integer parent packet.
- `inherited/PAYLOAD_BINDING.json`: unchanged source tuple binding needed by the
  coefficient verifier.
- `upstream/pell-congruences-source/`: retained original parent package, including
  its own proofs, generators, licenses and original reports.
- `provenance/`: relevant source-61 proof and repository comparison snapshots.
- `SOURCE_PROVENANCE.json`, `SHA256SUMS`: repository pins and release integrity.

Repository snapshot:
`cfbf118b4ad9b2c651fe96b571d9415261766328` of
<https://github.com/VladimirReshetnikov/ProveIt>.
Parent archive:
`docs/incoming/con_zfc_pell_congruences_2026-10-23.zip`.
Its SHA-256 is
`7c21ff5d05ef52c754399a6e62f37ac7622baa6e82a702d855bfb68d82fc1a4a`.

Prepared as AI-assisted research for Vladimir Reshetnikov and the ProveIt project,
23 October 2026. Preserve the inherited license and attribution files when
incorporating the contribution.
