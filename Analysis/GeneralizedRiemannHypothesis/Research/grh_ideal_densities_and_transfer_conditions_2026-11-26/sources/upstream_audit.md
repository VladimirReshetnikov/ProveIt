# Source audit and Selmer interface correction

Audited snapshot: **lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207**, as returned by the GitHub plugin on 2026-11-26.

## Files in this archive

Paths in this list are relative to the directory containing report.tex.

- sections/sha_odd_bridge.tex: complete report section, without a preamble.
- sources/audit_findings.json: exact source anchors, endpoint scope, audit limitations, corrected prior claim, and remaining obstructions from the initial source audit.
- sources/upstream_manifest.json: Git blob SHA and SHA-256 for 31 exact upstream files.
- sources/upstream/: 25 selected Lean files and six documentation/license files. Apache 2.0 license, NOTICE, and attribution are retained. These are selected snapshots, not a complete buildable upstream project.
- code/check_module_bridge.py: standard-library-only finite checks.
- data/module_bridge_checks.json: resulting verification record.
- verification/module_bridge_checks.log: recorded successful replay.
- sections/validation.tex: verification scope and commands for all supplied checkers.

## Most consequential finding

The readable edition's TwistedLengthLe already bounds the **full divisible Selmer module with coefficients Frac(O')/O'**. The intermediate precision is not a restriction of this final output.

The earlier report grh_beyond_dirichlet_2026-11-25/grh_beyond_dirichlet/sections/hecke_selmer.tex correctly describes the displayed compact theorem as finite precision, but its resulting blanket obstruction does not apply to the readable endpoint. Moreover, the compact theorem's same selected twist upgrades to the full divisible bound whenever its error satisfies B_i + η < M. This follows from a saturation lemma actually formalized and used in the readable source.

No interchange of a universal precision quantifier and an existential twist is needed. The Selmer modules are torsion modules and their finite-level versions are the corresponding torsion submodules. An arbitrary schematic countermodel that does not preserve this structure cannot establish the claimed obstruction.

## Positive extraction

The paper section proves that the source's exact strict odd-cocycle functor commutes with finite scalar extension from Z_l. Every condition is a homogeneous Z_l-linear equation, and a finite basis of O transports continuity and all conditions coordinatewise. This includes l=2 because no odd-part projector divides by 2.

For a fixed field E, prime l, Tate exponent j, and integer B ≥ 0, the source's all-precision/all-coefficient bound B is equivalent to the single test

    length_Z_l A_{l,j,B+1}(E;Z_l) ≤ B.

This is a concrete simplification of the missing noncyclotomic input. It does not prove that the test holds, compute the groups, remove the infinitely many prime conditions, or produce a field-uniform height bound.

The prior ramification_budget.tex already proved generic normalized-length invariance under scalar extension. The new completed step here is verifying the actual scalar-extension identification for shaOdd, not claiming the generic algebra as new.

## Exact finite checks

Running

    python3 code/check_module_bridge.py --output data/module_bridge_checks.json

passes 46,332 saturation checks, 50,193 finite-certificate equivalence checks, and 30 finite cyclic-cocycle scalar-extension models, including oddness at l=2. These checks verify finite model identities and edge cases. The mathematical proofs are in the TeX section. They do not calculate arithmetic Galois cohomology and do not verify the GRH development.

## Audit limits

This is **static source inspection**. Lean and Lake are not installed in the available environment. No full Lean build or independent kernel replay was run. The source's own README reports those checks and the standard-axiom dependency list; that report is not presented as a new local verification.

The selected Lean files have no declaration-level axiom, opaque, unsafe, sorry, sorryAx, or admit matches. This selected-file scan is not a transitive dependency or kernel audit.

The public endpoint is Dirichlet GRH, including imprimitive Dirichlet characters. General Hecke, Artin, and nonabelian Dedekind zero-location theorems are not among the five public endpoint statements.

