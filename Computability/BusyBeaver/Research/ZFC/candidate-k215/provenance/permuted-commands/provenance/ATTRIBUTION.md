# Attribution and scope

This new research contribution was prepared with ChatGPT for Vladimir Reshetnikov's ProveIt project. The new work consists of the 202-subtree command-specific input construction, the native state-81 helper-path reuse, the two successful command permutations, the exact 216-state tables, their independent audits and reproducible packet, and the new report sections that describe and prove those changes.

The dominated-rho8 theorem, propositional certificate, numerical calculus, proof-search architecture, arithmetic macro contracts, source language, and symbolic runtime infrastructure are inherited work. In particular, the dominated-row theorem reproduced in the report appendix is copied verbatim from the predecessor and is not claimed as a new contribution here.

The immediate predecessor is the unchanged `K217_Dominated_Continuation_2026-10-20.zip`, taken from ProveIt commit `8a1796545e33bf0c4bb52b6c92a6ced17362ca66`. It is retained under `parent/` and contains the unchanged `K218_Dominated_Rho8_2026-10-20.zip`. Their exact SHA-256 hashes are recorded in `inputs.json`. The predecessor's original attribution is reproduced in `PREDECESSOR_ATTRIBUTION.md`; the K218 notice is reproduced in `K218_NOTICE.md`. All embedded notices and licenses are retained.

The predecessor credits the architecture and machine work to Mira and the ProveIt project, the Rocq reference to Jeff's busy-beaver project, the compact theory K and K230 work to Elliot Glazer, and compiler ancestry to Andrew James Wade's Turing Machine Explorer. It also records BusyCoq and the Coq Library of Undecidability among the proof/calculus ancestry. Those original notices specify the exact scope of each contribution.

`code/build_dominated_source.py` and `sections/inherited_dominated_core.tex` are copied unchanged from K218. `source/baseline219.json` is the unchanged source input carried by that archive. `code/build_sources.py` and `code/audit_command_permutation.py` use the inherited structured-control/address-counter verification method, with new reconstruction, permutation, and selector/return-wrapper checks. The runtime checker is executed from the pinned nested archive rather than silently copied or modified. The independent source audit imports the unchanged `source_language.py` from the immediate predecessor.

The allocation witnesses document how the tables were found. Reproduction and certification use deterministic row recipes and the exact literal table; users need not trust or rerun a numerical optimizer.

New material is provided under the same MIT No Attribution terms as the ProveIt predecessor; see `licenses/LICENSE.ProveIt`. This does not relicense inherited third-party components, whose original licenses and notices remain authoritative.

There is no newly compiled exact-K216 Lean/Rocq endpoint, internally checked PA theorem, absolute consistency proof, state-minimality theorem, or universal discovery-priority claim. Independent parallel review denotes separately implemented checks and mathematical review within this collaboration, not an external human endorsement or independent authorship claim.
