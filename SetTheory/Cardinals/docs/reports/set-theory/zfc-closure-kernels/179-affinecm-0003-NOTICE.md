# Attribution and scope

This research and verification packet was prepared for Vladimir Reshetnikov's
ProveIt project on 21 October 2026. Its reviewed repository revision is
`56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`.

The numerical calculi and consistency calibration, the primary K215 Turing
machine and register programs, the source segment semantics, normalized
certificates and path tools, the proposed affine decomposition, the CM215
machine and transport design, and the proposed three-induction Lean refactor
are inherited ProveIt work. Their original authorship and license terms remain
unchanged. Relevant notices and license texts are retained in the component
directories. The source manifests identify byte-exact originals and deliberate
compatibility changes.

New work in this packet consists of the generic checked drain/contraction
library, checked source/graph adequacy and literal bindings to both current
programs, the explicitly recorded integration and compiler verification work,
the quiet-Lake identity patch, recorded applications of existing certificate
batching methods, and the new state-reduction experiments,
independent counterexample audits and analysis. The accompanying report
distinguishes these additions from the earlier proposals.

The 367-vertex affine graph is a semantic proof interface, not a binary Turing
machine with 367 or fewer replacement states. CM215 is an existing 215-state
design whose endpoint is attached and checked here. The 214-state no-append
table and the three provider-sharing tables are **rejected uniform-runtime
research experiments**. No correct
214-state consistency machine, unconditional nonhalting theorem, proof of
ZFC consistency, or state-count lower bound is asserted.

New original code and documentation in this packet are provided under the
MIT No Attribution terms in `LICENSE`. Inherited material retains the
individual license and notice terms preserved with each component.
