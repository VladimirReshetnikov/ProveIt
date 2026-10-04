# Integer-only fixed-arity sandpile certificate

## Result

One explicit integer polynomial with **2,566 positive integer witnesses**, **degree18**, and **11,469 paid arithmetic gates** represents finite global stabilization with binary odometer for a directly encoded periodic-plus-finite threshold-six sandpile on Z³. The single ordinary positive input is a fixed Cantor code of eight physical-instance descriptors. Unknown prism dimensions are quantified values. No time horizon or dimension-dependent witness list remains.

The full proof is `PROOF.md`; the authoritative source is `evidence/polynomial-dag.json`. The new builder uses only addition, subtraction and multiplication. All masks, powers, geometric repetition, finite-input reshaping, boundary padding and variable site conjunctions are paid. The substantial inherited number-theoretic dependency is the explicit fifteen-equation constructive Pell representation of powers, authenticated to the pinned mathlib source.

The key simplification is existential: a finite binary stabilizing supersolution bounds the true legal odometer by least action. Ranks are unnecessary to certify that stabilization exists. This does **not** identify the supplied supersolution with the true odometer and does not certify target firing. Full fibers are neither unique nor finite-fold, and no real-exactness is claimed.

## Scope boundaries

- The raw periodic tile and finite addition array are fully decoded in the polynomial
- The certificate covers natural nonnegative configurations, with stable periodic tile digits0–5 and patch digits0–15. Binary-stabilizable inputs automatically have initial heights at most11
- The patch is anchored in nonnegative coordinates; translating an arbitrary finite patch by period multiples preserves stabilization and allows this representation
- The particular Report35 literal graph, one-shot theorem and program-to-U15 compilation remain inherited. This work does not newly execute or reconstruct that enormous loader, and does not supply a separately paid raw-U15-word-to-physical-code arithmetic circuit
- This is a semantic fixed-arity compression result, not an improvement to the repository's84-operation universal polynomial

## Reproduction

The code below is newly authored for this packet. It reads no upstream executable source and invokes no universal-machine simulation.

    python3 build_certificate.py --output new-output-directory
    python3 check_source.py
    python3 check_exact_degree.py

The first command emits the same fixed polynomial from any working directory; dimensions are never command-line inputs or builder loop bounds. The other two read the authoritative evidence and write their own receipts. Normal and optimized (`python3 -O`) source replays from `/` are byte-identical. The authoritative DAG SHA256 is

    2e2403097ba0fb65bad349222246157bccad4ac59e99d594b48fa7a678a93723

## Evidence and provenance

`evidence/build-receipt.json` gives the full gate/equality/witness ledger and liveness check. `evidence/source-check-receipt.json` checks emitted macro substitutions, positive-domain examples, single-polynomial assembly, and five actual isolated Pell witness tuples. `evidence/exact-degree-receipt.json` contains the exact univariate specialization proving degree18.

The independent subproblem proofs and finite checks are in `stream-products/` and `periodic-input/`. These include binomial-parity masks, full-digit block spreading, padding, background repetition and all four generic tensor reshapes. Their optimized AND cost is deliberately not substituted into the authoritative source. Finite fixtures corroborate the proof and source interface; they are not full astronomical witnesses for the universal loader.

`sources/` contains byte-identical pinned mathematical source files as inert text. Source hashes are in `sources/source-pins.json`. A separate final source/theorem audit is in progress; this packet is not labeled independently approved until that report is received.
