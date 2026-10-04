# Periodic collision macros: science handoff

Research prepared on 4 October 2026. The full proof is `PROOF.md`, SHA-256 `df7cefb472a76e6f34ce7fff0b1e8548782a82f4863fac2ecd2d682c69941a77`. The proof is retained unchanged after an independent mathematical PASS.

## Result

A supplied repeated complete collision macro in a number-conserving rational signal machine with at most four live signals has an exact infinite-validity test consisting of linear and quadratic integer sign conditions in its initial gap numerators. A literal deterministic sign compiler turns this test into an ordinary sum-of-squares polynomial of degree at most four with exactly one natural witness tuple on each accepted input. All constants and arity are fixed after the machine and finite macro are fixed; no repetition bound enters the polynomial.

The same construction distinguishes finite-time accumulation from infinite elapsed time, using the clock observable rather than the spectral radius of the whole return matrix. For any fixed finite population, a valid ultimately periodic rational macro can have only rational finite accumulation times and rational limiting collision sites.

The actual four-signal example proves two useful cautions. Strict conditions at every finite collision may have a weak limiting boundary; and a neutral spectator coordinate can give return spectral radius one while the clock is summable. At the limiting boundary every finite prefix is legal. Nothing here defines a continuation through the accumulation instant.

## Exact scope

- The signal-machine definition requires pairwise distinct speeds within each incoming/outgoing collision set. Simultaneous disjoint sites and multiple collisions are included; all tied events and all incident signals are mandatory
- The return section is anchored immediately after a collision, with the same outgoing ordered label word and co-location pattern after each macro. An arbitrary observation phase is not retained
- The quartic construction is single-fold for each supplied integer input encoding. Equivalent rational descriptions with different common denominators are different inputs; no uniqueness across such descriptions is asserted
- The machine and supplied finite macro are compiler data, not additional polynomial input variables. Arity may grow with macro length
- No arbitrary-run liveness theorem, general recurrence positivity algorithm, population minimality theorem, new MRDP result, or post-accumulation semantics is claimed
- No general machine/macro parser or chamber frontend was implemented. The proof specifies one mathematically. The implemented emitter starts from a supplied degree-two sign formula

## Files and execution boundary

- `PROOF.md`: full self-contained statements and proofs, complete-batch conditions, recurrence classification, quartic construction, Zeno test, explicit example, rational-limit obstruction, and citations
- `check_arithmetic.py`: newly authored exact recurrence/sign/clock checks, using only the standard library
- `arithmetic_receipt.json`: 7,938 rational diagonal-mode comparisons; 882 Jordan/nilpotent comparisons; 45,000 arbitrary integer-matrix prefix probes; 15,147 trichotomy assignments; 6,912 displayed return-map identities; 64 strict-endpoint/late-failure checks; 66 clock-sum identities; 12 Boolean-gate cases
- `emit_sign_certificate.py`: newly authored sparse integer-polynomial sign compiler and exact checks
- `exports/four_signal_quartic.json`: actual four-signal infinite-validity predicate `d>0 and 2y>=d`, with complete residuals and expanded quartic: 10 natural witnesses, 15 residuals, degree 4, 65 monomials. This deliberately exercises the general compiler; the example also has the smaller elementary quadratic printed in the proof
- `exports/quadratic_sign_quartic.json`: nonsquare-spectrum recurrence diagnostic using AND, OR and NOT: 17 witnesses, 24 residuals, degree 4, 117 monomials. It certifies positivity of the first coordinate of `[[2,-1],[-1,1]]^n (x,y)` at every natural n for natural x,y. This is a recurrence diagnostic, not a claim that that matrix is a complete physically realized collision macro
- `exports/sign_compiler_receipt.json`: both expanded quartics passed 8,774 expanded-polynomial versus residual-sum comparisons, including 7,936 rejected one-coordinate witness mutations
- `SOURCE_NOTES.md`: retrieval scope, commit pin, literature and duplicate boundary
- `sources/`: inert repository text read during source/duplicate checks. None is imported by either new program

All infinite equivalences and witness uniqueness are mathematical proofs. Finite checks are supporting regression evidence. The checked 48-term integer-matrix sample happened to witness every rejected predicate within that prefix; no finite cutoff theorem follows from that observation.

No upstream program, downloaded code, saved computation schedule, or physical simulator was executed. The two new programs were read before execution. They contain no physical event-selection engine. The emitter's own sparse arithmetic expands residual polynomials; the other checker evaluates newly specified rational linear recurrences and displayed algebraic identities.

## Independent mathematical review

The separate review packet is `/workspace/shared/periodic-signal-independent-audit-20261004/`. Its auditor read the complete proof, retained its reviewed snapshot, found no substantive mathematical correction, and independently checked degeneracies, ties, canonical witnesses, clock cancellation and the spectator example. Those checks did not execute upstream or physical simulation code. The review is an independent research audit, not Lean/Rocq verification or peer review.

## Reproduce the new arithmetic only

From an empty scratch output directory:

    python -I -B check_arithmetic.py > fresh_arithmetic_receipt.json
    python -I -B emit_sign_certificate.py --output-dir fresh_exports

The emitter writes exactly the two named polynomial JSON files and its receipt below the specified directory. Its demonstration interface is not a hardened untrusted-input parser. No source package or signal-machine program needs to be executed.
