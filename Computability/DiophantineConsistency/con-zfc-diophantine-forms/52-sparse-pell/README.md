# Sparse quadratic coding and shorter Pell finalizers

Read report/report.pdf and the editable report/report.tex first. Construction snapshot: ProveIt commit 124c07c0b77a9e20e84676514d8b1ff78536ea3f. A separate postscript records later formalization status at 2d7766807b92f6d505649885d472e20cc0236b4f.

## Recommended equations

The domain is part of each claim. Degree and operation counts below are exact for the fixed supplied tuple. Operations are live binary addition, subtraction, and multiplication, including multiplication by literal constants; all repeated squaring and fixed powers are charged.

- Nine positive integers, recommended compromise: nine/generated/nine_174_interior_shifted_positive.json; degree 10,486,092; 603 operations.
- Nine positive integers, lowest cost: nine_174_interior_regular_positive.json; degree 15,502,748; 548 operations.
- Nine positive integers, lowest degree: nine_174_interior_packed_positive.json; degree 10,127,484; 655 operations.
- Their separately translated nonnegative-domain forms have the same degree and three more operations.
- Ten unrestricted integers, recommended compromise: integer/generated/sun10_interior_packed_shifted_homogeneous.json; degree 34,378,296; 637 operations.
- Ten unrestricted integers, lowest cost: sun10_interior_regular_homogeneous.json; degree 50,822,936; 582 operations.
- Ten unrestricted integers, lowest degree: sun10_interior_packed_global.json; degree 33,202,776; 689 operations.
- Eleven positive integers: positive/positive11_Y_lean_product.json; degree 954; 113 operations. Two-equation system: maximum degree 952; 108 operations after the justified transport shift.
- Twelve positive integers: positive/positive12_none_lean_product.json; degree 897; 108 operations. Three-equation system: maximum degree 888; 102 operations after the justified transport shift.

The new contributions are sparse-active quadratic isolation, irregular targets and interior padding, a positivity-first norm with conditional radical separation, a sharp polynomial Pell majorant, exact CRT quotient removal, shared homogeneous source evaluation, and a lean positive carrier with smaller Y-absorption modulus. The coefficient radix 2^590069 is inherited from the complete tuple in packages 39/44 and is not a new size record.

Each equation's lack of solutions in its stated domain is provably equivalent in ZFC to Con(ZFC), by the ordinary mathematical arguments and the pinned inherited compiler/arithmetic dependencies. This is not a proof of consistency, a global minimum, a new unknown-count theorem, or a new end-to-end Lean/Rocq/object-level ZFC derivation artifact. The complete formal K215 development is not bundled.

## One-command sealed verification

Requires Python 3.10+ and the packages listed in requirements.txt. From any working directory:

    python /path/to/extracted-release/verify_release.py

The default command rejects -O/-OO, checks the exact delivered file set and all file hashes, validates every retained source Git blob, and then runs eleven authored finite checks in an isolated temporary copy. The sealed original remains unchanged. No network, TeX, Lean, Rocq, upstream program execution, or installation is needed for this check.

For integrity alone, explicitly add --integrity-only. That does not replay the mathematical checks. Run negative_controls.py to test optimized-execution rejection, missing/extra/corrupt files, a tampered collision certificate, and a rehashed source corruption. The root RELEASE_HASHES.json is integrity metadata, not a digital signature.

## Rebuilding

Rebuild only in a working copy: builders and individual checkers regenerate receipts and may write outputs. To retain the seal, keep the extracted release unchanged and use the default isolated verifier.

- Coefficients: python review/check_native_independently.py, then python review/check_parent_coefficients.py.
- Sparse certificate checks: python packing/verify_certificate.py.
- Nine circuits: see nine/README.md for the complete certificate argument list; then run nine/materialize_coefficients.py and nine/verify_nine.py.
- Ten circuits: python integer/build_integer.py, then python integer/verify_integer.py.
- Positive circuits: python positive/build_absorbed.py, then python positive/check_absorbed.py.
- PDF on a normal TeX Live or MiKTeX installation: change into report and run pdflatex report.tex twice, or latexmk -pdf report.tex. report/build.sh is a Linux research-environment fallback with explicit system font paths, not a portable Windows script. It uses no shell escape. The delivered PDF is verified without TeX.

## Files and trust boundary

All fixed leaves are ordinary integers, not unknowns. coefficients/ contains the four native unsigned little-endian values; use the entire coherent tuple. MF_source is already shifted. nine/COEFFICIENT_INSTANCE.json and integer/FIXED_BINDING.json specify all compressed derived payload encodings, signs, and hashes. JSON circuits are division-free DAGs. Their named registers do not add witnesses. Degree-certificate DAGs may be larger than the primary evaluator; their cost is not substituted into the claimed operation count.

packing/ includes every finite positional certificate and an independent standard-library symbolic checker. audit/ includes independently authored whole-circuit and exact shared-source audits. positive/Y_ABSORPTION_PROOF.md is the full parallel mathematical proof. review/ contains 42 current source pins and source texts; inherited/ contains the 83-file historical proof collection and separately pinned ratio/signed proof references. review/postpin/ is a distinct four-document status snapshot, not a claim of newly checked formalization.

Dominated nine/ten source variants remain as reproducible comparisons, not recommendations. No heuristic search executable, TeX cache, transient log, or Python cache is included. Licenses and notices are retained; see LICENSE and NOTICE.md.
