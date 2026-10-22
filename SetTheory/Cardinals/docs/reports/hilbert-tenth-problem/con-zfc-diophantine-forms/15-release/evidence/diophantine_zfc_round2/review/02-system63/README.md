# A fixed Diophantine representation of Con(ZFC)

**Recommended result:** seven polynomial equations in **16 strictly positive
integer unknowns**, maximum degree **28**, evaluated by a shared circuit of
**63 binary arithmetic operations**. For the exact fixed coefficients in this
packet, ZFC proves

\[
\text{the system has no positive integer solution}
\quad\longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

Read [report.pdf](report.pdf) for the complete construction and mathematical
proof; [report.tex](report.tex) is its compilable LaTeX source. This packet is
prepared for incorporation into Vladimir Reshetnikov's ProveIt repository.
All inherited sources are pinned to commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

## Available presentations

| File | Unknown domain and count | Equations | Exact degree | Shared arithmetic operations |
|---|---|---:|---:|---:|
| `fixed_input63_ordinary_system.json` | 16 positive integers | 7 | maximum 28 | 63 |
| `fixed_input74_ordinary_square_marker.json` | 16 positive integers | 1 | 101 | 74 |
| `fixed_input72_square_marker.json` | 16 positive integers | 1 | 157 | 72 |
| `positive16_sos.json` | 16 positive integers | 1 | 56 | 83 |
| `integer64_sos.json` | 64 unrestricted integers | 1 | 112 | 211 |
| `quadratic_lift.json`, `equations` field | 79 nonnegative integers | 70 | maximum 2 | not counted |
| `quadratic_lift.json`, `quartic` field | 79 nonnegative integers | 1 | 4 | not counted |

The final 72/74 sources are equivalent to the system **in existence of positive
solutions**, not equality of their individual zero tuples. They use a squared
budget residual equal to one. The old 73/75 sources are retained as proof
parents; their marker is one plus the squared residual. The seven-equation
system and its quartic lift keep the exact zero-budget comparison.

The operation convention charges every binary addition, subtraction and
multiplication, including squares and arithmetic with fixed numerals. Reuse
and equality comparisons are free. It does not charge the bit length of fixed
coefficients. No global minimum claim is made: the repository's existing
`Jones1982.nine_unknowns` theorem already gives a smaller-variable existence
result, without providing the concrete short coefficient packet delivered here.

## Mathematical specification

The sixteen positive unknowns are

\[
J,F,\alpha,t,f,h,i,T,s,w,\tau,\eta,\zeta,y,Z,\gamma.
\]

The five fixed coefficient ports are `Bm1`, `Kconstant`, `MC`, `MF`, `W0`.
They mean \(B-1,K,M_C,\overline M_F,W_0\), respectively. The source name
`MF` is **the shifted mask** \(M_F^{\rm nat}+B-1\), not the native mask.
Every abbreviation in the report expands polynomially; no abbreviation is
an additional existential variable. Every exponent in the coefficient recipe
is fixed and independent of the Diophantine unknowns.

The coefficient recipe is fully specified by
[constants.md](constants.md), [fixed_constants.json](fixed_constants.json),
[fixed_compiler.py](fixed_compiler.py), and the exact finite machine/window
definition [normalized_k215.py](normalized_k215.py). In particular,

\[
b=5^{43},\qquad d=5^{87},\qquad B=2^d,\qquad W_0=2^{2d+b}.
\]

The exact tile alphabet has size 3502 and the exact allowed-window count is
`20522746353535702537070419760`. The list starts with the two distinguished
windows and then all other valid nine-tuples in lexicographic order. A fixed,
terminating enumeration defines every coefficient; there is no unspecified
program index or oracle. **The actual huge list, correction bit, and expanded
K215 coefficient numerals have not been computed.** The integer B alone has
approximately \(6.46\times10^{60}\) bits. Do not invoke the actual iterator
expecting a practical numeral export.

The normalized machine erases its unary input and then simulates the exact
blank K215 machine. Arithmetic input 1 corresponds to **raw machine input 2**,
represented by four initial ones. This is why the marker is fixed at W0.

## Reproduce the finite checks

Python 3.10 or later and its standard library are sufficient. From this directory:

```sh
python3 reproduce.py
```

To save a fresh combined receipt elsewhere:

```sh
python3 reproduce.py --receipt /tmp/zfc-diophantine-checks.json
```

This checks upstream source/notice hashes, replays the 72/74 source changes and
their 73/75 parents, independently rechecks the final product sources, validates
the folded machine, tests the finite compiler on small fixtures, regenerates
the entire quartic, independently compares every quartic coefficient, and
regenerates the positive/integer sum-of-squares variants. It does not enumerate
the actual enormous window list or expand the actual K215 coefficient tuple.
It writes temporary generated controls outside the packet and leaves the
recorded deliverables unchanged.

The machine validation deliberately rejects Python `-O`, because its exhaustive
checks use assertions. The arithmetic source and quartic validators use explicit
exception checks and also pass with optimization enabled.

To compile the report:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively run `pdflatex report.tex` until cross references stabilize.
The report uses standard TeX Live packages. The supplied PDF has been rendered
and visually checked. `SHA256SUMS` gives hashes for the distributed files;
check it with `sha256sum -c SHA256SUMS` before regenerating any output.

## File map

| Group | Main files |
|---|---|
| Main exposition | `report.tex`, `report.pdf`, this README |
| Recommended system and final compact equations | `fixed_input63_ordinary_system.json`, `fixed_input74_ordinary_square_marker.json`, `fixed_input72_square_marker.json` |
| Parent arithmetic sources | `fixed_input75_ordinary.json`, `fixed_input73.json`, `fixed_input63_system.json`, `complete84_scaled_strong_output.json` |
| Proofs of the new reductions | `FIXED_INPUT73_PROOF.md`, `FIXED_INPUT75_ORDINARY_PROOF.md`, `SQUARED_MARKER_PROOF.md`, `PELL_INTERFACE_LEMMAS.md` |
| Arithmetic checkers | `verify_fixed_input.py`, `verify_fixed_input_ordinary.py`, `verify_square_marker.py`, `check_square_marker_review.py` |
| Machine and coefficient specification | `k215.tm`, `normalized_k215.py`, `normalization.md`, `constants.md`, `fixed_constants.json`, `fixed_compiler.py` |
| Compiler comparison controls | `test_fixed_compiler.py`, `explore_fixed_raw_universal_76.py`, `complete75_half_binomial_compiler.py` |
| Quadratic/quartic presentation | `QUADRATIC_LIFT.md`, `quadratic_lift.py`, `quadratic_lift.json`, `check_quadratic_lift_review.py` |
| Positive and unrestricted-integer SOS presentations | `emit_sos_variants.py`, `positive16_sos.json`, `integer64_sos.json` |
| Receipts and reviews | `*_checks.json`, `*_validation.json`, `REVIEW_*.md`, `reproduction_checks.json` |
| Inherited proof excerpts and source provenance | `RAW75_PROOF.md`, `ASYMMETRIC_SCALE.md`, `PELL_RELAXED_AUXILIARY_PROOF.md`, `complete*.md`, `NineMain.lean`, `PROVENANCE.json` |
| Attribution and terms | `ATTRIBUTION.md`, `UPSTREAM_NOTICE.md`, `upstream_licenses/` |

Original upstream Markdown links inside copied proof files may refer to other
parts of the pinned ProveIt checkout; the archive is not a full repository mirror.
`PROVENANCE.json` supplies exact immutable source URLs. Some working copies
contain one additional terminal LF; both local and upstream hashes are recorded.
The literal K215 table and authenticated parent F84 JSON are byte-exact.

## Verification status and logical scope

The pinned K215 endpoint has upstream external Lean and Rocq proofs calibrating
blank halting against ZFC refutability. The new equation proof combines that
calibration with the repository's mathematical Pell and finite-window compiler
theorems. **This contribution does not contain a newly compiled end-to-end
Lean or Rocq proof of the Diophantine equivalence.** No proof-assistant build
was rerun here. The exact imported interfaces and source paths are identified
in the report and proof notes.

The executable checks validate arithmetic transformations and finite program
details. They do not establish ZFC consistency, K215 nonhalting, or an actual
positive solution. Small diagnostic coefficient tuples in tests are algebraic
controls, not claimed valid ZFC compiler instances.

Assuming ZFC is consistent, the equations have no solutions in the specified
standard integer domain, and their unsolvability is not provable in ZFC.
Independence in both directions needs a stronger soundness hypothesis; bare
consistency alone is not stated to suffice.

For repository incorporation, preserve the mathematical proof status, source
pin, exact coefficient specification, domain declarations and inherited notices.
New material is intended for the repository's MIT No Attribution terms;
inherited components retain their own notices. See `ATTRIBUTION.md`.

