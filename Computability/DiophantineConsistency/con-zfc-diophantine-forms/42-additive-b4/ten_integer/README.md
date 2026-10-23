# B4-coded consistency equation in ten unrestricted integers

Main equation: `generated/b4_signed10.json`.

* Unknowns: 10, all unrestricted integers.
* Exact total degree: **107286763576**.
* Arithmetic operations: **2204** binary +, -, and *.
* Mathematical statement: ZFC proves that no integer solution exists if
  and only if Con(ZFC), using the inherited K215/compiler endpoint and
  Sun's 2026 ten-integer bridge.
* New contribution: source monomial exponents use a finite B4 additive
  code in place of positional powers of five. The old source degree is
  589042901992797851562527064; the new degree is smaller by a factor of
  approximately 5.49e15, at a cost of 762 additional circuit operations.

Read `PROOF.md` for the new adapter, precise dependencies and limitations.
`upstream_SIGNED10_PROOF.md` is a historical copy of the inherited
outer bridge/finalizer proof; its old source-coding section is superseded
here. Its filenames and old reproduction commands refer to that source
package, not to the active entry points below.

Reproduce from this directory, with only the Python standard library:

```bash
python3 b4_code.py
python3 build_b4_sun10.py
python3 verify_b4_sun10.py
```

The third command overwrites the generated circuits with exact-degree
metadata and writes `generated/VERIFICATION.json`. It validates the fixed
coefficient payloads and source polynomial, the finite B4 certificate,
formal norm identities, modular transcription comparisons, and nonzero
leading-degree coefficients. These finite checks supplement the ordinary
proof. They do not prove consistency or form an end-to-end formal
verification of the imported machine/compiler and Lucas theorems.

All active coefficient definitions are in `data/INSTANCE.json`,
`data/constants.json`, `data/coefficients_binding.json` and
`bose_chowla32.json`. The source polynomial has 31 natural witnesses;
the alpha vectors keep an initial zero solely to preserve the inherited
coefficient-record convention. That zero does not occupy a coding digit
and is not an extra unknown.

The other generated variants preserve universal norm weights or the
literal four-square Sun finalizer for comparison. They use the same B4
source and complete coefficient tuple. No polynomial in this package is
asserted to have globally minimal degree, description size or unknown count.

Provenance and attribution: `SOURCE_PINS.json`, `NOTICE.md`, and `licenses/`.
