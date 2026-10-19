# Reproduction guide

## Default offline replay

```sh
python3 -B verify.py --output /tmp/zfc-below245-replay
```

The output directory must be new or empty. Python assertions are required. The default checks use Python's standard library and the attributed backend already in the package. The dependency archive is checked against the hard-coded SHA-256 before safe extraction; its own 293-file integrity list is then replayed by the retained verifier.

The root replay writes separate logs under the chosen output directory and checks subprocess exit codes **and** explicit JSON assurance statuses. For each principal semantic candidate it compares fresh machine tables, allocation, renumbering, source sites, source bisimulation, and entire blank-frame certificate byte-for-byte with the delivered frozen files. Timing metadata is not treated as mathematical evidence.

The final JSON is `verification-summary.json`. Its `requested_sub245_endpoint_achieved` field is false. A successful replay establishes the reported research results and expected failures.

`results/integrated-replay-before-packaging.json` records the successful integration run before the final payload manifest was generated; its payload-hash count is therefore zero. Running the command above on the delivered archive also checks every entry of the included `SHA256SUMS` before starting the mathematical and machine checks.

## What runs by default

1. Verify package hashes and the unmodified source68 dependency.
2. Rerun the pinned 245-state delivery's core verifier: exact tables, source bisimulation, actual-table arithmetic induction templates, all 8,391 affine guarded cases, independent successor-frame closure, scanner contraction, and exact blank initialization.
3. Rebuild the canonical 245-state representation control and prove literal table relabeling.
4. Rebuild the relaxed 245-state grammar, with 50 retained bootstrap equations, and check its entire runtime/frame/blank chain.
5. Rebuild the related 244-state scanner experiment; require the recorded affine failure and successful blank prefix.
6. Rebuild the complete 252-state five-zero witness at padding 96 and check its source/runtime/frame/blank chain.
7. Recompute the exact zero-five obstruction under the original 54 locks and replay the initial abstract control plus 10 frozen grammar certificates.
8. Independently replay the original-grammar 244-state scanner's blank prefix and its wrong-successor family, with arbitrary additional gap and arbitrary nonempty spare suffix.
9. Reproduce all finite formula-codec, matrix, and equivalent-CP raw compiler controls. The raw tables remain explicitly partial; they are not candidate consistency machines.

No heuristic search is necessary for these checks. The new arithmetic frame verifier imports no source decoder or symbolic executor; it checks pointer normalization by integer arithmetic and reconstructs the entire initialized tape. The combined replay first runs the separately required source, macro, symbolic, and bootstrap checks, then consumes their outputs.

## Optional expensive checks

```sh
python3 -B verify.py --full-scanner-audit --output /tmp/zfc-scanner-full
```

This repeats the expanded symbolic scan over all 8,391 guarded cases to reproduce all 99 failed scanner-contraction premises. It takes several minutes. The default already reproduces the uniform wrong-successor family, and checks the frozen full-audit summary's structure.

```sh
python3 -B verify.py --whole-frame --output /tmp/zfc-frame-full
```

This repeats the inherited expanded arbitrary-register/spare-list proof on the **new relaxed 245-state table**, with its independently certified source sites. It is a separate, slower proof expansion. The default uses the actual-table macro induction certificates and complete all-parameter affine driver. The report and summary explicitly distinguish a fresh optional expansion from retained prior evidence.

```sh
python3 -B verify.py --search --output /tmp/zfc-elimination-replay
```

This additionally compiles and reruns the stated finite elimination screens. It requires `g++` with C++17 support. The inherited 8,385 literal fixtures are unpacked from the pinned compressed corpus, and executables are created only in the new output directory. The two context-specific searches that hit budgets are reported as bounded, not exhausted. See `research/framework/README.md` for exact domains and limits.

## Optional heuristic optimization

Search commands are in `research/grammar/README.md`. The C++ annealers require C++17. Their wall-clock stopping rule and unordered-container iteration can change search trajectories across machines; use frozen candidates for deterministic verification.

The optional finite dictionary MILP scripts use NumPy and SciPy/HiGHS. The broad warm-start model uses an internal HiGHS interface and may require adaptation with a different SciPy version. Solver status is an experimental result for the explicit finite pool, not a proof of the unrestricted optimum. The package's finite replay does not depend on SciPy.

## Build the documents

```sh
make pdf
```

This runs `pdflatex` twice for the integrated report and twice for the standalone theory/codec note. Required TeX packages include Latin Modern, AMS mathematics, geometry, booktabs, enumitem, microtype, fancyhdr, xurl, xcolor, and hyperref. The document build was checked with TeX Live 2023 and pdfTeX 1.40.25.

To render for visual inspection with Poppler:

```sh
pdftoppm -png -r 110 report.pdf /tmp/zfc-report-page
pdftoppm -png -r 110 research/theory/theory_codec_note.pdf /tmp/zfc-theory-page
```

The delivered PDFs have been rendered and visually inspected. Generated TeX auxiliaries and reproducible binaries are not part of the frozen payload. Rebuilding a PDF can change its metadata bytes, so a rebuilt document will need a refreshed `SHA256SUMS` if it is to replace the frozen one.

## Proof scope

The package supplies ordinary mathematical proofs with executable certificates. The recursive set-theory/proof-calculus calibration is retained from the pinned source68 package, including its upstream attribution. The new machine transfer arguments compose it with separately checked source bisimulation, positive universal runtime segments, complete frame closure, and exact safe blank initialization. No new Lean, Rocq, or internally generated PA proof object is supplied.

The Hκ model proof and local first-order CP equivalences are ordinary unbounded arguments. The finite matrix is exhaustive for its stated three-valued propositional semantics. Codec tests and raw compiler comparisons have their exact finite coverage recorded, and do not substitute for an unprovided proof-search calibration of those variants.
