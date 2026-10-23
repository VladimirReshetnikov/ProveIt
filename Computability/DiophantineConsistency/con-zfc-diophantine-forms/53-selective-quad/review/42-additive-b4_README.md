# Additive coding and smaller coefficients for Con(ZFC)

An explicit research contribution for the ProveIt collection, prepared
23 October 2026 against commit
**22e75dd6b87b1b199bb08c778d7cf075ae5aae08**.

Read [report.pdf](report.pdf) for the complete mathematical report.
The editable source is [report.tex](report.tex), with substantive sections
in [sections/](sections/). All equation coefficients and arithmetic circuits
are included; there is no unspecified recursively enumerable set index.

## Main result

The recommended polynomial in
[ten_integer_composed/generated/b4_signed10.json](ten_integer_composed/generated/b4_signed10.json)
has exactly ten unrestricted integer unknowns and satisfies

    ZFC proves:
    (there is no integer zero of F_B4) <=> Con(ZFC).

Here Con(ZFC) uses the same syntactic proof predicate as the pinned
repository. The equivalence is proved in ordinary mathematics formalizable
in ZFC, using the explicitly identified inherited machine/compiler,
quartic, and Sun bridge theorems.

| Measure | Pinned package 31 | New B4 instance |
|---|---:|---:|
| Unrestricted integer unknowns | 10 | 10 |
| Exact total degree | 589042901992797851562527064 | **107286763576** |
| Binary arithmetic operations | 1442 | **2204** |
| Complete coefficient tuple | package 31 | new nonzero-code tuple |

The degree decreases by a factor of approximately **5.49036 × 10^15**,
at a cost of 762 extra arithmetic operations. This is a substantial degree
improvement with the variable count fixed; it is not a new
variable-count theorem or a claim of global optimality.

### The mathematical idea

For a quartic parent, positional exponents 5^j do much more than is needed.
It suffices to distinguish sums of at most four positions. A classical
Bose–Chowla B4 code, translated to include zero, supplies 32 positions
with maximum 942302. The positive 31 positions encode the existing
31 source witnesses; zero homogenizes the fourth power.

For the fixed source polynomial P0(n)=sum p_alpha n^alpha, define

    c_alpha = (4-|alpha|)! product(alpha_i!) p_alpha
    D(t) = sum c_alpha t^(4T-alpha.w),     T=942302.

Then the coefficient of t^(4T) in

    (1+sum n_i t^w_i)^4 D(t)

is exactly 24 P0(n). The report proves all digit bounds, mask decoding,
the reverse implication, and the complete source interface needed by
the unchanged ten-integer outer construction. For fixed source degree d,
the general mechanism reduces the coding span from exponential in the
number n of source variables to O(n^d). The code is classical;
the new contribution is the explicit replacement and audited
composition in this consistency instance.

## Separate coefficient improvement and simpler arithmetic forms

[coefficient_backend/](coefficient_backend/) contains a new complete
native compiler tuple. Encoding every edge label x by x+1 reserves zero
for emptiness and makes four separate occupancy bits unnecessary.
A shorter exactly checked synchronization layout gives:

| Measure | Pinned smallest tuple, package 36 | New tuple |
|---|---:|---:|
| Base | 2^1012115 | **2^683195** |
| Largest port, bits | 1016946 | **688546** |
| Four raw coefficient payloads, bytes | 506664 | **342269** |

The raw payload size drops by **32.45%**. All four ports are replaced
together. Their actual unsigned little-endian integers, compressed
copies, hashes, finite recipes and proof are included.

Two concrete presentations are bound to this new tuple:

| File in coefficient_backend/equations/ | Domain | Equations | Degree | Operations |
|---|---|---:|---:|---:|
| product67_nonzero683195.json | 15 positive integers | 1 | 155 | 67 |
| retained16_system59_nonzero683195.json | 16 positive integers | 7 | maximum 24 | 59 |

For each presentation, ZFC proves that absence of solutions in the
stated domain is equivalent to Con(ZFC). The arithmetic graphs are
inherited; their new fixed coefficients are the improvement.

The recommended composed ten-integer circuit uses this new tuple.
Its 402 weighted coefficient recipes and all bounds have been regenerated,
with a new source radix multiplier 2^2743514. The five raw fixed
payloads, including that multiplier, total 685209 bytes, compared with
1066835 for the original binding, a reduction of 35.77%.

The separate comparison circuit in
[ten_integer/](ten_integer/) retains the complete package-31 tuple and
isolates the additive-code change. It has the same degree and 2204-gate
shape. The two instances have distinct fixed data and verification receipts.
The arithmetic DAG alone does not identify the polynomial: its fixed-leaf
names must be resolved through the companion data/INSTANCE.json and actual
coefficient payloads. Both complete bindings are included.

## Reproduce

Python 3.10 or later with only the standard library is sufficient:

    python3 reproduce.py

The driver rebuilds and checks both constructions in a fresh temporary
copy, compares regenerated outputs byte for byte, runs the independently
written auditors, and writes a deterministic REPRODUCTION.json receipt.
It does not alter the published equation files. Its complete transcript
is shown if a step fails. The checks run in seconds to minutes depending
on the machine.

Individual entry points:

    python3 ten_integer/b4_code.py
    python3 ten_integer/build_b4_sun10.py
    python3 ten_integer/verify_b4_sun10.py
    python3 coefficient_backend/build_coefficients.py
    python3 coefficient_backend/audit_coefficients.py
    python3 coefficient_backend/verify_equations.py
    python3 review/audit_b4_independent.py
    python3 ten_integer_composed/regenerate_binding.py
    python3 ten_integer_composed/b4_code.py
    python3 ten_integer_composed/build_b4_sun10.py
    python3 ten_integer_composed/verify_b4_sun10.py

The individual generators operate in their own directories; run the
top-level driver when a nonmutating isolated check is preferred.

Build the PDF using a conventional TeX Live installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The report uses standard packages, including amsmath, amsthm, mathtools,
mathrsfs, lmodern, booktabs, microtype, enumitem, xurl and hyperref.
The Makefile provides verify, pdf, archive and clean targets.
To verify delivered file hashes, run:

    python3 package_release.py --check

After deliberate edits, rebuild and run reproduce.py, then
package_release.py to generate a fresh manifest and ZIP.

## What was checked

* All 52,360 four-element multisets of the displayed additive code;
  their sums are distinct as integers and modulo 1,048,575.
* Exact reconstruction of 402 weighted source-coefficient records from
  the 22 literal shifted residual squares, with actual fixed-payload
  hashes and a proved coefficient bound.
* Formal norm identities, literal-formula versus circuit transcription
  diagnostics, variable lists, fixed leaves, and gate liveness.
* Exact degree: a gatewise upper bound and a nonzero diagonal
  leading coefficient with the actual constants. For the recommended
  composed circuit this coefficient is 36 modulo 101, 63 modulo 1009,
  and 258712 modulo 1000003. For the original-tuple comparison it is
  16, 599, and 622356 respectively. Any one nonzero residue suffices.
* Independent coefficient reconstruction, 59,902 scalar native-basis
  identities, both synchronization intersections, carry bounds, masks,
  padding and the actual-rank controller.
* Exact binding of the P67 and 59-operation graphs, including the
  main-norm cancellation needed for the advertised degree.
* Independent mathematical reviews of the B4 adapter and new backend.

The finite checks have their stated scope. They do not decide
consistency, replace proofs of unbounded equivalences, or constitute
a new end-to-end Lean/Rocq formalization. The ten-integer theorem has
an explicit dependency on Sun's 2026 preprint.

## Repository incorporation

This directory is suitable as a new sibling of packages 31–37 in
the collection. Keep the inherited polynomial identities and source
names distinct from the new instance. MANIFEST.json records delivered
file hashes. SOURCE_LEDGER.json identifies additional reviewed source
copies; each subpackage has its own detailed provenance and licenses.

The report also records further research directions and unsuccessful
shortcuts. In particular it makes no claim of a nine-integer equation,
an improved nine-natural-variable circuit, a smaller quartic witness
count, or worldwide novelty of the additive combinatorics.

See [NOTICE.md](NOTICE.md) and the retained licenses before incorporation.

