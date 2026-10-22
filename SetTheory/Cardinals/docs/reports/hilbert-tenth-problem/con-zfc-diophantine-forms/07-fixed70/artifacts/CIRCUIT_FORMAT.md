# Circuit format and reproduction guide

`fixed_input.py` generates and checks five literal arithmetic circuits in
`fixed_input.json`. The preferred compact polynomial is `fixed70`; the
`transparent61` packet gives eight equations with a simpler interpretation.
The main report and `fixed_input_notes.md` prove the mathematical reductions.
The program checks the emitted arithmetic, its dependencies, and its counts.

The five compiler coefficients are fixed by `compiler/COEFFICIENTS.md`.
They are supplied as numeral ports, not as existentially quantified variables.
They have enormous exact finite specifications. Neither the gate counts nor
the reproduction checks include expanding these integers in decimal or
enumerating the entire finite window list.

## 1. Reproduce the receipt

Python 3 and its standard library suffice. From the root of this packet, run:

```sh
python3 artifacts/fixed_input.py --output /tmp/fixed_input_fresh.json
```

The script resolves `parent84_reference.json` relative to its own location,
so the command also works from another working directory when the script path
is absolute. Preserve that adjacent reference file. It is authenticated by
SHA-256 before the source is used.

For a byte-for-byte comparison with the checked-in receipt, run from the
packet root:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib

saved = Path("artifacts/fixed_input.json").read_bytes()
fresh = Path("/tmp/fixed_input_fresh.json").read_bytes()
if saved != fresh:
    raise SystemExit("Receipt differs")
print("Identical receipt:", len(saved), "bytes")
print("SHA-256:", hashlib.sha256(saved).hexdigest())
PY
```

The receipt shipped with this packet has 45,975 bytes and SHA-256

```text
a8042fde1907a58623c21c6cacf390039e6b44c22152281fd0032a298557c464
```

The script's successful exit and `status: PASS` mean that all its explicit
checks passed. They do not constitute a proof-assistant verification of the
compiler or of the equivalence with consistency.

To reproduce the two fully explicit domain conversions of `fixed70`, run:

```sh
python3 artifacts/domain_variants.py --output /tmp/domain_variants_fresh.json
```

This standalone script reads only the adjacent `fixed_input.json`; an
alternative path can be supplied with `--input`. It verifies the input hash
and emits complete 86-row and 198-row circuits, including every substitution
gate. Compare the fresh output with `artifacts/domain_variants.json` in the
same way as the first receipt above. The generated packet names are
`fixed70_nonnegative16` and `fixed70_integer64`; both use the same source
schema and `output = "polynomial"`. The generator checks dependencies,
liveness, exact operation counts, unchanged original rows, and 32 exact
arithmetic fixtures per variant. Each fixture compares all 70 original
registers with direct evaluation after substitution, including a fixture
whose new witness coordinates are all zero.

## 2. Receipt and packet schema

The top-level JSON object has these fields:

| Key | Meaning |
| --- | --- |
| `status` | `PASS` after the checks finish successfully. |
| `parent` | Pinned parent URL, commit, exact file hash, and embedded source hash. |
| `circuits` | Metrics keyed by packet name. |
| `exact_integer_fixture_count` | 32 deterministic iterations, each checking several arithmetic identities. |
| `degree_diagnostics` | Deterministic univariate specializations over two finite fields. |
| `proof_boundary` | Explicit scope of the executable checks. |
| `packets` | The five complete source packets. |

Select a packet by name instead of relying on its array position:

```python
import json
from pathlib import Path

receipt = json.loads(Path("artifacts/fixed_input.json").read_text())
packet = next(p for p in receipt["packets"] if p["name"] == "fixed70")
rows = packet["source"]
output_register = packet["output"]
metric = receipt["circuits"][packet["name"]]
```

Each packet declares `witness_domain`, `witnesses`, `fixed_numerals`, and
`source`. Polynomial packets also declare `output`; the system packet
declares `comparisons`. A source row has exactly four entries:

```json
["new_register", "*", "earlier_register", 4]
```

The operator is `+`, `-`, or `*`. An operand is either an exact JSON integer
or a string naming a witness, a numeral port, or an earlier register. Register
names are unique and there are no forward references. Each row computes its
value once, and later rows may reuse that value without a charge.

Every multiplication, including a square or multiplication by a fixed
numeral, contributes one to `M`. Every binary addition or subtraction
contributes one to `A`. Thus `total = M + A = len(source)`. Reading a port,
reusing a register, and the final equality test are not arithmetic gates.
The structure checker also verifies that every row and every supplied port
contributes to an output or a declared comparison.

The source is a definition by abbreviations of an ordinary polynomial.
Registers are not additional existential unknowns in the stated witness
count. If one instead introduces a variable for each register and an
equation for each gate, that is a different, larger polynomial system.

### Numeral ports

| JSON port | Mathematical value |
| --- | --- |
| `Bm1` | `beta = B - 1`. |
| `Kconstant` | `K = DC + B DR`. |
| `MC` | The modified compiler's low mask. |
| `MF` | `MF_shifted = MF_native + B - 1`. |
| `W0` | `2^b B^2 = 2^(2*5^89 + 5^44)`. |

Here `b = 5^44`, `d = 5^89`, and `B = 2^d`. All remaining finite
definitions, including the compiler's correction bit, are specified in
`compiler/COEFFICIENTS.md`. Substituting the unshifted `MF_native` into the
`MF` port changes the construction. Positivity of arbitrary port values
does not establish that they are coefficients of the required compiler.

### Witness ports

For `fixed70`, `fixed71`, and `fixed73`, the 16 witnesses are:

```text
Jrep, F, alpha, transport_quotient, f, h, i, auxiliary_quotient,
s, w, tau_root, eta, zeta, y_aux, Z, gamma
```

Their report names are respectively

```text
J, F, alpha, t, f, h, i, T, s, w, tau, eta, zeta, y, Z, gamma.
```

For `transparent61` and `transparent84_sos`, the 17 witnesses are:

```text
J, F, alpha, z, Z, f, h, i, j, o, s, w, tau, eta, zeta, gamma, y
```

The `z` in the transparent system is the physical transport quotient; it
is not the sheared quotient `transport_quotient` used by the compact
polynomials. The witness correspondences are proved in the mathematical
notes, rather than implied by common register names.

## 3. Final equations and exact metrics

| Packet | Positive witnesses | Equations | M | A | Total | Polynomial degree |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `fixed70` | 16 | 1 | 40 | 30 | 70 | 169 |
| `fixed71` | 16 | 1 | 40 | 31 | 71 | 156 |
| `fixed73` | 16 | 1 | 41 | 32 | 73 | 157 |
| `transparent61` | 17 | 8 | 33 | 28 | 61 | At most 28 per residual |
| `transparent84_sos` | 17 | 1 | 41 | 43 | 84 | 56 |

For a packet with `output`, its equation is the value of that register
equal to zero. The compact polynomials use `output = "polynomial"`.
The sum-of-squares polynomial uses `output = "sum_7"`.

For `transparent61`, impose all eight pairs in `comparisons` as equalities.
An integer operand in a pair denotes the literal integer; a string denotes
the corresponding register. The receipt's metric `comparisons: 0` for the
other packets means that they use a single output equal to zero, not that
they impose no equation.

The conversion from `transparent61` to `transparent84_sos` explicitly adds
eight residual subtractions, eight squares, and seven additions. Its output
is the sum of those eight squared residuals. Thus the conversion adds 8
multiplications and 15 additions, giving 84 total arithmetic operations.
Over integers, this sum is zero exactly when all eight comparisons hold.

### The compact polynomial's finalizer

For `fixed70`, the seven entries of `factor_outputs` are

```text
norm_first, norm_main, norm_repunit, norm_aux,
norm_index, norm_transport, norm_strong.
```

Their exact degrees are respectively `24, 20, 1, 64, 8, 2, 50`.
The circuit multiplies these seven factors and subtracts the register `A`.
Here `A` denotes the positive Pell discriminant `Delta`; it is not the
report's Pell parameter or the addition count in the metrics table.
Writing `S` for the product of the first six factors, the exact identity is

```text
polynomial = S*norm_strong - Delta
           = Delta * (S*(f^2 - Delta*i^2*c^4) - 1),
```

where `c` is the register `R10a` and `Delta` is the register `A`.
The same scaled identity holds for `fixed71` and `fixed73`, with their own
factor lists. At a positive solution, the mathematical proof recovers the
first six factors as 1 and `norm_strong` as `Delta`. Setting all seven
scaled factors to 1 would impose the wrong equation.

The field `gate_degree_upper_bound` is computed by the elementary rules
`degree(x*y) = degree(x)+degree(y)` and
`degree(x +/- y) <= max(degree(x),degree(y))`. It does not detect cancellation,
so its values 173, 160, and 161 for the three compact polynomials exceed
their exact degrees 169, 156, and 157. The report and mathematical notes
give the cancellation and leading-form arguments. The finite-field
specializations in the receipt are reproducible diagnostics and do not
replace those arguments for the actual compiler coefficients.

## 4. Positivity and conversions of the witness domain

Every witness in the original packets ranges over the strictly positive
integers. This is part of the equation's specification. Intermediate
registers may be signed away from solutions. The proof restores the needed
signs at zeros; a consumer must not add independent positivity constraints
on every intermediate value.

Directly reinterpreting the witness ports as arbitrary integers is also
incorrect: the compact finalizer includes a factor `Delta`, and positivity
is needed to justify cancellation and subsequent Pell arguments. Use an
explicit domain conversion if a different convention is required.

### Nonnegative witnesses

For each positive witness `v`, substitute `v = n + 1` with `n >= 0`.
Compute this expression once and reuse it. This adds one addition per
witness, leaves the witness count unchanged, and preserves the degree.

| Packet | Nonnegative witnesses | Equations | M | A | Total | Degree |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `fixed70` | 16 | 1 | 40 | 46 | 86 | 169 |
| `fixed71` | 16 | 1 | 40 | 47 | 87 | 156 |
| `fixed73` | 16 | 1 | 41 | 48 | 89 | 157 |
| `transparent61` | 17 | 8 | 33 | 45 | 78 | At most 28 per residual |
| `transparent84_sos` | 17 | 1 | 41 | 60 | 101 | 56 |

### Unrestricted integer witnesses

For each positive witness `v`, introduce four independent integer witnesses
and substitute

```text
v = 1 + u1^2 + u2^2 + u3^2 + u4^2.
```

Lagrange's four-square theorem ensures that every positive integer is
represented. Conversely, the displayed expression is always positive.
Computing it once costs four multiplications and four additions. It
doubles the degree bound. Only witnesses are replaced; the five fixed
numerals retain their prescribed values.

| Packet | Integer witnesses | Equations | M | A | Total | Degree bound |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `fixed70` | 64 | 1 | 104 | 94 | 198 | 338 |
| `fixed71` | 64 | 1 | 104 | 95 | 199 | 312 |
| `fixed73` | 64 | 1 | 105 | 96 | 201 | 314 |
| `transparent61` | 68 | 8 | 101 | 96 | 197 | 56 per residual |
| `transparent84_sos` | 68 | 1 | 109 | 111 | 220 | 112 |

These tables give exact gate counts for the stated direct substitutions,
without additional optimization. They are not claims of globally minimal
counts. The degree of `fixed70_integer64` is **exactly 338**. To see this,
let `H` be the original polynomial's nonzero leading homogeneous form of
degree 169. The degree-338 part after substitution is
`H(sum_j u_1j^2, ..., sum_j u_16j^2)`. Setting the last three coordinates
of each group to zero, and calling the first coordinates `z_1,...,z_16`,
restricts it to `H(z_1^2, ..., z_16^2)`. Distinct
monomials of `H` remain distinct when every exponent is doubled, so this
restriction is nonzero. The complete degree-338 part is therefore nonzero
as well. Translating the witnesses by 1 similarly preserves `H` and exact
degree 169 for `fixed70_nonnegative16`.

`fixed_input.json` contains the original positive-witness circuits.
`domain_variants.json` contains the two complete conversions of `fixed70`,
including their exact degrees, substitution maps, metrics, source hashes,
and reproduction-check scope. Conversions of the other four packets remain
specified by the substitutions and counts above.

## 5. Evaluating and checking an emitted packet

The module exposes `fixed70()`, `fixed71()`, `fixed73()`, `transparent61()`,
`sum_of_squares(packet)`, `evaluate(packet, values, positive=False)`,
`structure(packet)`, and `verify()`.

`evaluate` accepts a mapping with exactly the declared witness and numeral
keys. Values must be Python integers; booleans and floating-point values are
rejected. It returns all supplied and computed register values. The optional
`positive=True` checks positivity of every supplied port. The default
permits signed assignments for arithmetic identity tests. Neither mode
certifies arbitrary supplied numeral values as compiler coefficients.

`structure` checks acyclic dependencies, unique outputs, valid operators,
and liveness before returning the metrics. A caller evaluating a modified
packet should first check its structure and source identity: `evaluate`
alone does not authenticate arbitrary caller-provided source.

`verify` authenticates the pinned parent, reconstructs the five canonical
packets, checks their operation counts and witness counts, runs seeded
exact-integer arithmetic checks, and runs the modular degree diagnostics.
The exact-integer fixtures test identities even at signed assignments; they
are not purported solutions of the Diophantine equation. The small numeral
choices in the degree diagnostics are explicitly not the ZFC compiler
instance.

The metric `source_sha256` hashes the `source` array using

```python
hashlib.sha256(
    json.dumps(source, sort_keys=True, separators=(",", ":")).encode()
).hexdigest()
```

It differs from the hash of the whole JSON file and deliberately excludes
descriptive metadata. The preferred circuit's source SHA-256 is

```text
458aa30130504edf7e00b6a4aea294a6dbab110d904032d19ff8803a651ad96f
```

For an independent arithmetic comparison, see
`review/review_fixed70.py`, `review/FIXED70_REVIEW.md`, and the accompanying
`review/independent_review.json`. The mathematical soundness and completeness
arguments, the machine normalization, and the coefficient specification
remain separate parts of the deliverable.
