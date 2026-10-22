# Explicit Diophantine forms for Con(ZFC), wave 3

This package provides fixed, fully instantiated integer polynomials and systems
whose absence of solutions in the stated domain is proved equivalent in ZFC
to Con(ZFC), by ordinary mathematical reduction through blank-input K215.
Read `report.pdf` or `report.tex` for the synthesis and the companion proof
notes for the detailed arguments.

## Main improvements

- `amalgamation/main_root12_product.json`: 12 strictly positive integer
  unknowns, 123 binary arithmetic operations, exact degree 1145.
- `arithmetic/polynomial13_84_smallweight.json`: 13 strictly positive integer
  unknowns, 84 operations, exact degree 515.
- `arithmetic/integer27_product136_smallweight.json`: 27 unrestricted integer
  unknowns, 136 operations, exact degree 1004.
- `domains/integer54_quartic.json`: 54 unrestricted integer unknowns, a
  degree-4 polynomial given as the sum of squares of 31 quadratic residuals.
- `domains/integer45_degree6.json`: 45 unrestricted integer unknowns, a
  degree-6 polynomial given as the sum of squares of 22 residuals.
- `domains/integer39_degree8.json`: 39 unrestricted integer unknowns, a
  degree-8 polynomial given as the sum of squares of 16 residuals.

The six primary smallweight files are the product, four-equation system and
sum-of-squares variants for each of the 13-positive and 27-integer domains.
`INSTANCE.json` lists these, the root12 product and the 54/45/39-variable
low-degree forms as primary artifacts. Its secondary list contains the
higher-weight 27-integer forms, alternate root12 system/sum-of-squares
forms, the dominated 46-integer octic and the other domain frontier points.
These secondary variants are retained for comparison and identity checks,
not as replacements for the recommended smallweight forms. Circuit operations count every binary addition,
subtraction and multiplication, including multiplication by a numeral.
Abbreviations and gate registers are definitions, not extra unknowns.

## One exact coefficient tuple

`INSTANCE.json` fixes the numerical instance for all 19 main polynomial
packets. Every packet and its builder selects the same complete tuple:

- Tuple ID: `T4-4094-binary-copy-zero-padding-5pow11`.
- Tuple SHA-256: `726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938`.
- Base: B = 2^(5^11) = 2^48828125.
- Canonical port order: beta, K, MC, MF_source.
- Aliases: Bm1/beta means beta; Kconstant/K0 means K; MC means MC;
  MF means MF_source, the shifted source mask MF_native + B - 1.

The four exact integers are `coefficients/expanded/{beta,K,MC,MF_source}.bin`,
encoded as unsigned minimal-width big-endian integers. Together they occupy
25,421,252 bytes. Their bit lengths, populations and individual hashes are
in `coefficients/expanded/MANIFEST.json` and `coefficients/COEFFICIENTS.json`.
The tuple digest is SHA-256 of the ASCII concatenation of their four
lowercase file hashes in canonical port order. It is not a digest of a JSON
serialization. The recipe is closed and finite; no free coefficient remains.

`coefficients/COEFFICIENT_PROOF.md` proves the whole-tuple transfer, including
canonical parity, positive odd i and positive square w. Do not mix any port
with an older compiler's numeral. Old recipes, including
`domains/ORIGINAL_COEFFICIENTS.json`, and bindings in vendored source packets
are historical evidence only, not the selected instance. Main packet
metadata keeps that provenance separate from `coefficient_binding`.

## Reproduce all checks

Run from the extracted package root. The checks were tested with Python 3.12
and SymPy 1.14.0; the arithmetic builders and coefficient checks otherwise use
only the Python standard library. No network access is used by the verifier.

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py
```

Do not run with Python `-O`: some component programs deliberately use
assertions. The root verifier rejects optimized execution.

`verify.py` first validates the shipped binary files, bit populations, tile
count, literal transition export, every main packet's coefficient binding,
variable and operation counts, source hashes and live registers. It then
copies the mathematical payload to a temporary directory, replays only our
new builders and independent audits, checks byte-for-byte agreement of
rebuilt packets and receipts, completely reconstructs the coefficient files,
and runs a separate independent compact audit. Original artifacts are not
overwritten; only `VERIFICATION.json` is written at the package root.

Three additional integrity controls deliberately corrupt one numeric byte, the shifted-mask alias, and the literal transition table in a temporary copy. Run `python negative_controls.py`; all three must be rejected. This writes `NEGATIVE_CONTROLS.json`. These are integrity tests, not semantic counterexamples.

For a fast check without replay:

```sh
python verify.py --quick
```

This writes `VERIFICATION.quick.json`, not the full receipt.

The literal `coefficients/sources/k215.tm` is included. The verifier compares
all 430 exported transitions against its ordered table, with movement
encoding L = -1 and R = +1, and checks the pinned hashes of both source files.
Only the compiler adds stationary padding after the original halt state.

Individual commands, if regeneration in place is desired:

```sh
python amalgamation/build_root12.py
python arithmetic/build_integer27.py
python arithmetic/build_smallweight.py
python domains/build_domains.py
python domains/build_tradeoffs.py
python review/check_root12_independent.py
python review/check_smallweight_independent.py
python review/check_low_degree_independent.py
python coefficients/load_coefficients.py
python coefficients/load_coefficients.py --rebuild
python coefficients/audit_compact.py --materialize
```

`load_coefficients.py --rebuild` runs the tile builder, independent count,
independent materializing audit and final metadata builder, then verifies
all four bytestrings. Programmatic users may add `coefficients/` to their
module search path and call `load_coefficients.load()` for the four Python
integers in canonical order. Expanding a whole high-degree polynomial with
these enormous coefficients is unnecessary.

Compile the report with a standard pdfLaTeX distribution including geometry,
AMS packages, booktabs, array and hyperref:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Evidence and boundaries

- Source snapshot: ProveIt commit
  `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`, notably packages 09, 11, 12, 14
  and 15 of the Con(ZFC) Diophantine collection.
- The main proofs are `amalgamation/ROOT12_PROOF.md`,
  `arithmetic/INTEGER27_PROOF.md`, `arithmetic/SMALL_WEIGHT_PROOF.md`,
  `domains/DOMAIN_REDUCTION_PROOF.md` and
  `coefficients/COEFFICIENT_PROOF.md`.
- `review/RATIONAL_AUXILIARY_PELL_LEMMA.md` supplies the rational-root
  integrality lemma. Independent formula and sparse-polynomial audits are
  under `review/`.
- Vendored documents, source packets and historical Python are evidence.
  The root verifier never executes or imports upstream Python. The new
  builders read upstream polynomial JSON only. The new coefficient programs
  read literal transition data only.
- Finite-field line specializations diagnose symbolic degrees; the uniform
  exact-degree and semantic statements rely on the mathematical proofs.
- No accepting K215 computation is constructed. No consistency or
  inconsistency of ZFC is proved. The universal Pell/compiler bridge and
  logical endpoint remain inherited mathematical dependencies.
- This is not a new end-to-end kernel-checked proof, and no global or
  restricted-class optimality is claimed. A shorter circuit, fewer unknowns,
  lower degree and smaller coefficients are different measures of size.

The source repository's notice is retained in `LICENSE.ProveIt`.
Exploratory dead ends are omitted from the package.
