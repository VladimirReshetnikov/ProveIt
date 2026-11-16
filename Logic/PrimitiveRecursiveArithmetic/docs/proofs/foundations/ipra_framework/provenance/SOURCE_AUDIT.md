# Source scope and provenance

## Pinned source

The repository source is [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt), pinned to commit
`42c64ff3a9f56f2a9edc1525e75ece3b720c7f77`.
The inspected local checkout was
`/workspace/scratch/93caf7830ecf/ProveIt-source`.

`source_manifest.json` identifies **31 selected consulted files**, with their full repository paths, original absolute local paths, pinned GitHub URLs, exact byte sizes, SHA-256 hashes, and Git blob SHA-1 hashes. Every recorded local source file was checked against its blob in the pinned commit. The paths record the authoring checkout; they are not a requirement that a reader recreate that directory.

Hash agreement establishes source identity. It does not establish that a mathematical assertion in a source is correct.

## Catalog versus review

`packet_catalog.csv` contains the **46 packet entries** in
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`.
It records the index's domain, path, description, archive wrapper, arrival, and file counts. Descriptions report what the packets say about themselves. Each row explicitly says that a full packet audit is **not claimed**.

The index reports 968 placed files and 77 omitted archive members. Counting the files actually present in all 46 packet directories at the pinned checkout confirmed each packet's placed-file count and the total of 968. The omitted archive members were not independently recovered or verified. The index itself says the packets were filed as delivered without rerunning, checking, compiling, or editing their contents.

The selected review concentrated on:

- ConciseIPRA's syntax, deduction rules, primitive recursive symbols, quantifier-free induction, and native/ordinary theory transport API.
- The Puiseux packet's exact-algebraic coefficient construction, weighted-norm convergence proof, and reported obstruction for arbitrary Cauchy coefficients.
- The calculus, Gamma, zeta, rotation, and dimension-invariance packets' stated representation interfaces and formalization boundaries; the zeta-zero report's explicit evidence levels; and the PNT logarithmic-integral report's finite arithmetic and precision-budget foundations.
- The Siegel packet's square Runge certificate and remaining general route; the Mordell–Weil packet's existing finite descent; and the Faltings/Roth distinctions between cardinality, finite windows, and positive height cutoffs.
- The prime-distribution packet's stated conditional Chebotarev reduction and its remaining Siegel–Walfisz/Bombieri–Vinogradov parameter estimates.

This is a selected-source review, not a verification of every theorem in any of those packets. Reading a README supports claims about a packet's stated scope and status, not independent certification of its proofs. The `review_role` field distinguishes such scope sources from mathematical proof sections and foundation source files.

## Inherited results and the present additions

The report reuses established ideas: bounded search, finite arithmetic representations, contraction, discrete power gaps, and metastability. It makes no mathematical priority claim.

The existing Puiseux source already contains a finite weighted-norm proof. The present branch construction extends its usable representation on a **certified regular chart**: it permits fixed primitive recursive Cauchy coefficients and an approximate center, using geometric contraction instead of exact coefficient stabilization. The report also completes a human proof of an explicit primitive recursive **certificate producer from supplied simple-root data**: a root name, coefficient and root bounds, and a quantitative derivative gap (or an inverse name with its bound). It constructs rational approximate center and inverse data, dyadic radii, majorants, and a passing contraction certificate with predetermined precision bounds. Thus certificate existence is proved for that stated input class. The producer's complete Lean proof remains a named formalization target. It does not find the initial root name or discover singular charts uniformly.

The selected PNT foundations already give fixed rational evaluators and finite precision-budget arguments. The common arithmetic-table interface organizes and generalizes this style of proof; it is not claimed as a new historical error-propagation method. The additional zeta-zero status source is used for its explicit separation of written mathematics, finite runs, and uninstantiated formal obligations.

The existing Siegel source already proves the square certificate and constructs it by rational square completion. The present theorem extends that certificate to all exponents `m >= 2`, proves an explicit power-completion constructor, classifies the additional family `y^m = x^(mr) + x + 1` for `m >= 3`, and proves transport with a supplied bound on rational denominators.

The existing Mordell–Weil packet already has a substantial contraction-descent theorem and a bounded selector under a true rational covering-list hypothesis. It is acknowledged as existing work, not counted as a new descent theorem. The existing Roth packet already distinguishes a finite empty window from a final cutoff. The report's common finite-contract interface makes those distinctions explicit and develops the bounded-monotone finite-window construction without claiming a general final modulus.

The copied foundational kernel is adapted from the pinned `Syntax.lean`, `Deduction.lean`, and `PR.lean`. Its limited import/notation changes and source-block comparison are recorded separately in `lean/UPSTREAM_SOURCES.json`. The repository license is MIT No Attribution; `lean/LICENSE-ProveIt.txt` preserves it. The selected original `NativeBiInterpretation.lean` API is consulted for the separate integration adapter, not silently assumed to supply new arithmetic proofs.

## Dependency and proof-status boundaries

An existing theorem transporting `Prf PRAAx` proofs requires an arithmetic proof as input. It does not turn a native Lean theorem, a numerical experiment, or an unchecked analytic record into an iPRA derivation.

The delivered archive distinguishes compiled native lemmas, the small explicit embedded proof examples, unproved named Lean targets, and the fully developed human mathematical arguments. Compilation of definitions or targets is not counted as proof of those targets. Exact finite program checks validate the tested implementation behavior; the written universal arguments remain separate.

A finite certificate checker does not establish that a passing certificate exists for every proposed input. Rational quotient representatives, uniform general height bounds, unrestricted denominator control, singularity classification, and major analytic parameter estimates remain substantive obligations where the source packets identify them. The present framework does not assert that their unresolved iPRA targets are impossible or independent.

## Reproduction

With a local checkout whose `HEAD` is the pinned commit, run:

```sh
python3 provenance/rebuild_provenance.py /absolute/path/to/ProveIt
```

The script reads that checkout and regenerates `packet_catalog.csv` and `source_manifest.json` beside itself. It checks the commit, every selected source blob, the 46-row catalog count, and all placed-file counts before reporting success. It does not modify the source repository. The absolute source paths in the regenerated manifest will reflect the reader's checkout.
