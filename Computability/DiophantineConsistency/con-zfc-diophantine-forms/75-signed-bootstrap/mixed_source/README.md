# Positive monic source projections

Run `python build.py 21`, `python build.py 24`, and `python build.py 26` to rebuild the three exact sources. Run `python check.py` for the independent identity/degree replay and corruption controls. Python 3 and SymPy are required.

The equations are fully specified by the JSON residuals and constants inherited from the pinned parent source. In each case, sum their squares to obtain a single ordinary polynomial. Unknowns range over strictly positive integers. They are not unrestricted-integer endpoints.

Deliverable files: README.md, PROOF.md, section.tex, parent_source.json, source21.json, source24.json, source26.json, build.py, check.py, verification.txt. Other files in this directory are exploratory and not part of the result.

Status: exact symbolic identities checked; positivity and composition proved mathematically; inherited compiler/source theorem not independently re-proved or kernel-checked here. No new compact positional endpoint, global minimality, or record claim.

Comparison: existing 20-positive octic and 25-positive sextic endpoints dominate the 21-positive octic and 26-positive sextic here in unknown count. These are transformation demonstrations, not record claims. Both builders and checkers retain validation under Python -O.

Explicit fixed instance: COEFFICIENT_BINDING.json selects the complete old31 tuple from the bundled ZFC_Diophantine_Oriented_Guards_2026-10-23.zip, with beta=2^1064921−1. This is NOT the low_degree compact44 tuple. The source hash matches the inherited nine/PROOF.md §1 exactly. The historical default metadata in frozen parent_source.json is retained for byte provenance; the new binding manifest is the explicit selection for these endpoints. From the package root:

    unzip incoming/ZFC_Diophantine_Oriented_Guards_2026-10-23.zip "ZFC_Diophantine_Oriented_Guards/nine/coefficients/old_tuple/*" "ZFC_Diophantine_Oriented_Guards/nine/upstream/old_tuple_complete_proof.md" -d extracted_coefficients

Decompress each gzip payload and interpret unsigned little-endian. K0=K and MF=MF_source already shifted; never mix separate bindings.
