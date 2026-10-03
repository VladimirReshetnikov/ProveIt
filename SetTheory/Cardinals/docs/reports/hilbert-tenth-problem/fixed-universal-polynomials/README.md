# Report 23 revision 1 — A fixed universal Grill polynomial

Read `article/report23.pdf` (23 pages). Editable LaTeX is `article/report23.tex`; `article/build.sh` rebuilds the PDF with a conventional installed LaTeX distribution. The complete scientific source and independent checks are in `reproducibility/`.

## Result and scope

One literal 397,488-phase Grill program gives one complete arithmetic polynomial with ordinary positive input and five program parameters fixed for each represented computably enumerable language. It has 797,135 positive witnesses and 3,600,546 operations: 803,517 multiplications and 2,797,029 additions/subtractions. Its exact total degree is 69,339,973. The original 71,731,007 remains a valid historical syntactic upper bound. Revision 1 proves an all-tuple cancellation and supplies the complete leading homogeneous form and explicit nonzero ray coefficient for the SAME polynomial; no source gate, coefficient, witness, comparison, or finalizer changed.

The exact-degree theorem is unconditional algebra on the pinned source. The language theorem remains conditional on the pinned full native/recoder and finite-input U15 theorems and applies to the explicit valid five-parameter slices. It is not a new general MRDP theorem or an optimality claim. No full giant Pell tuple or complete universal accepting execution is claimed to have been materialized. The costs use literal-integer arithmetic, not bit complexity.

The actual 61,209,290-byte DAG is included, not just its generator. Its SHA-256 is:

`a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`

## Offline checks

Python 3.10 or newer on Linux is required; only the standard library is used. The resource-limited checkers rely on Linux/Unix resource measurements. Allow about 1 GiB RAM, 250 MiB temporary disk, and several minutes. No network access or upstream Python execution is used.

From the extracted release directory:

```sh
python3 -B verify_release.py
python3 -B verify_release.py --replay
python3 -B -O verify_release.py --replay
python3 -B reproducibility/test_integrity.py
python3 -B -O reproducibility/test_integrity.py
```

These entry points also work from any CWD when passed their full extracted path. The replay writes only to a temporary directory outside the sealed release. It re-emits the complete DAG, compares its exact hash and scientific manifest, and runs all 15 original source/component/whole-circuit checks plus both new independent exact-degree verifiers. Normal and optimized Python both retain explicit invariant validation. The inventory is checked again after replay.

`RELEASE_INVENTORY.json` covers every delivered file, including the article, build script, proofs, audits, data, source, and portable code. Its digest is in `RELEASE_INVENTORY.sha256`. The nested reproducibility inventory is independently enforced. Added files, missing files, byte changes, undeclared empty directories, and symlinks are rejected. The separately supplied ZIP hash is the external distribution anchor; a local manifest cannot authenticate an attacker who replaces both files and all digests.

## Provenance and review

`reproducibility/PROVENANCE.json` keeps original frozen hashes separate from delivered hashes and transformations. `reproducibility/PORTABILITY.md` documents path sanitation, inert original-source naming, module-relative replay paths, assertion-to-exception changes, and staged metadata adaptations. This makes the release portable without falsely relabelling transformed bytes as original bytes.

`exact-degree/` contains the new frozen degree proof, independent review, certificates, checkers and a separate exact inventory. Its checkers read the existing full DAG via pinned relative paths; there is only one DAG copy. `qa/` contains the article review and portable-replay receipts; files prefixed `v0-` document the superseded original article, not the revised PDF. `REVISION.md` records the unchanged v0 artifacts and exact scope of this revision. Historical scientific audit files keep their original scope, including statements about work still pending when those audits were written. The complete composition proof and final whole-circuit audits record the completed mathematical and source result.

The delivered v0 directory, v0 ZIP and entire original reproducibility subtree remain byte-for-byte unchanged. No previous report or upstream repository was altered. A replay's bounded simulations and exact circuit checks support the implementation; the parametric proofs and explicitly imported full positive converses establish the unbounded theorem.
