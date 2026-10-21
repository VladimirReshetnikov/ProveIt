# Certificate composition and arithmetic summaries

This packet separates inspected upstream compiler evidence from new, independently checked finite computations and uncompiled theorem proposals. No new machine or state reduction is claimed.

## Reproduce

Run Python 3 with assertions enabled, from this directory:

    python -I -B verify.py --work /tmp/round10-check

Use a fresh external work directory. No network, Lean or Rocq is needed. Received archive scripts and proof modules are not executed. The owned static calculus rewriter is executed; it is not the received generator.

The replay verifies pinned payloads, regenerates the 1,426-node source graph and prior 367-node affine core, checks the 189-node arithmetic contraction, checks the concrete Rocq balanced-normalized composition and four mutations, regenerates proposed calculus text, and replays runtime row/dependency/tail checks.

Success is explicitly qualified: ten arithmetic edge regressions exhaust their finite budget. They are not successful executions or divergence proofs. All exact shape/composition checks complete; 14,418 local and 554 edge regressions complete. No proof-assistant compilation is performed here.

## Scope

- New Rocq composition: 1,426 entries, 2,851 branches, 32,961 balanced lookup visits instead of 2,033,059 list visits. This is not a measured build speedup. Lean already uses normalized balanced lookup.
- Arithmetic interface: 174 triangular and four conditional-clear loops summarized to 189 control nodes. Generic soundness remains an uncompiled mathematical argument.
- Quotient/generator proposals: share existing semantic theorems without weakening endpoint hypotheses. Proposed Lean files are uncompiled.
- Runtime: 6,012 unchanged traces and 139 fresh checks are conditional on box semantics. Append-zero requires generalizing the maintained increment-tail interpretation; agreement on 44 rows alone is insufficient. The six-step framed tail window is independently checked, not kernel-certified.
- Upstream phase 5 is an incremental 184-module closure, not a wholly fresh build. Its outer execution returned 143 after saved PASS evidence. One refinements dependency has a documented compatibility-source mismatch. Automatic certificates have bounded source/log audits, not a rebuilt full endpoint.

See report.pdf/report.tex for mathematical details and priorities. Review archives are inert provenance, not code to run. Nested notices/licenses and pinned input manifests preserve attribution. The top-level MANIFEST.json pins all payloads; it is an integrity inventory, not a mathematical proof.
