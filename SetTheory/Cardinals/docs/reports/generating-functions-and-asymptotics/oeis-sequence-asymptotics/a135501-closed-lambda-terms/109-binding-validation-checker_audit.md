# Independent finite-checker audit

2 October 2026; Python 3.12.14. **PASS for the exact script and data hashes below.**

## Findings

- The model uses leaf size s=0 or 1 and unit abstraction/application size. The admissibility relation, binder choices, maximum unary height, exact first moments, and finite bounds agree with the definitions in the report.
- The main suite passes normally and under `python3 -O`: **5,457 mathematical guard evaluations**, followed by exact comparison of all five snapshots and their data-directory inventory. Static inspection finds no removable `assert` statements in the six reviewed scripts and no floating-point literals in the mathematical checker. Numerical divisions are on `Fraction` objects; coefficient and combinatorial calculations are integers.
- Independence is stated at its actual scope. Size totals and moments are crosschecked by the bivariate recurrence through n=20; the radical transformation is checked on 825 distinct (m,k,b) triples, with 3,285 guard evaluations including repeats. Explicit skeleton/slot enumeration is a separate representation. The through-n=200 tables are not independently enumerated through that entire range.
- `validation/auditor_probes.py` materializes de Bruijn term sets, crosschecking both models' totals and moments through n=7 and 20 small height histograms. It explicitly instantiates 318 lower-height constructions and materializes all **52,465 reduced shapes through u=9**, checking their deficit majorization, squared products, shape weights, and maximum-product recurrence. Its **105,711 mathematical guards pass in both modes**.
- Twelve additional inventory guards per mode pass on disposable inputs: valid baseline, duplicate JSON keys, boolean schema/size, unsafe path, invalid digest, extra files (including nested build/qa), missing/changed files, and symlinks. The boolean-size test uses a zero-byte file, so accidental `False == 0` acceptance would be exposed.

## Corruption and replay

The frozen campaign was independently executed in an isolated package snapshot. All **26 cases / 52 normal-and-optimized runs** were rejected: nine mathematical source faults, seven fixture faults, and ten manifest/inventory/hash faults. Mathematical cases bypass the manifest and must reach their named mathematical guards. Covered faults include model initialization, parity, Catalan and uniform bounds, height statistic and lower witness, deficit product, shape recursion, and radical denominator. A separate abstraction-size/binder mutation and root-slot omission were also rejected during development.

The campaign first checks pristine integrity in both modes, freezes one hash-checked copy, clones each case, rejects syntax-only failures, and verifies originals unchanged. The unmodified full checker and post-campaign integrity both passed normally and with optimization. Results are recorded in `auditor_results.json`.

Replay source was reviewed for duplicate/unsafe/symlink archive rejection, exact archive inventory, normal/optimized mathematical checks and independent probes, then rebuild and PDF-byte comparison. Final PDF rendering and the completed delivery-ZIP replay are separate assembly checks; this audit does not certify later file changes.

## Limits

Only 16 published prefix terms per model were externally verified; complete remote OEIS b-files were unavailable. The longer tables are internally computed. `--fixtures-only` deliberately checks just prefixes through n=20 and table lengths; it is not a full snapshot or inventory check. Hashes provide consistency relative to the manifest, not authentication. These finite tests do not prove asymptotic statements, establish error thresholds, or certify novelty.

## Reviewed SHA-256 hashes

- `check.py`: `14d3db34cc36a22d035f10bd9165df13961da4537b29d3b02cbf2f3fca1cd360`
- `integrity.py`: `b3fe4ceccb3733b21463aa70bd4499d0966fe1d41ae8ff003762a84402fb5bcc`
- `corruption_test.py`: `8fd0e590cfd9b0ad5808559231e32e2882617a6f93fbd73104f26be740f4215e`
- `replay.py`: `4001794c382070638ef10942c80439a40355e0e748de585fc4e328e2507549f1`
- `build.py`: `b0688328bd38d51b8fd611c62bd40940e824aecb60ad5adda56c99070ab73ec3`
- `validation/auditor_probes.py`: `4d5005420dbfccc483c3558d377148a21a755785a44362a23d61c53e6e56dc37`
- `data/A135501_computed.txt`: `73407065f64f8ccf57c5b6c1667fefb9d8f0b0523ad2544361497a304b0b6112`
- `data/A135501_unary_moment.txt`: `bfc1c4415a2817e5dd4404b09d174b10dec36c4d6158c2e1e7ecd419cf9b3d05`
- `data/A220894_computed.txt`: `80396c6724bd5d1d5d0b1636c7a92e5bc059cc31ef315f3704234856bab30fa2`
- `data/A220894_unary_moment.txt`: `9d0f9664aeba9a9f159fb0ff855ffea0c91cc48f4159ab95e675d586a51a414c`
- `data/check_results.json`: `b78760fb73341c640519b8eeafb75918595fed77696997e5ae1755adf2f0d60b`
