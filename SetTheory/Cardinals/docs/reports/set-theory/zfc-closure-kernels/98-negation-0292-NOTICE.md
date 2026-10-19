# Attribution and provenance

This research contribution was prepared on 18 October 2026 for the ProveIt
investigation of a small ZFC-consistency Turing machine. The pinned ProveIt
commit is `fd1adfa19f8fe8da41444e3fa43b89a59d891067`.

The source program and calculus are attributed to Mira-Cult. The upstream
formal verification is attributed to Jeff Ketchersid, and the compiler
framework to Andrew James Wade. Existing licenses and notices in the archive's
`dependencies/fine_grammar/runtime/reference` remain applicable.

`vendor/` retains selected earlier ProveIt research scripts and its original
notice. The old notice's relative `reference/zfc245` path describes its source
package; in this combined archive the corresponding inherited materials are
under the dependency and reference directories recorded by the main manifest.

`anneal_trace_ideal.cpp` adapts the inherited attributed trace annealer. It adds
general trace-ideal left/right quotients and explicit child commutation.
`anneal_fine_routing_closed.cpp` adapts the byte-preserved
`vendor/anneal_fine_compound_hardened.cpp`; it adds an atomic-terminal barrier
to route projection checks and a complete projection recheck after garbage
collection. `routing-closure.patch` records the exact local change.

The Python source/route preparation, LM emitter, independent finite audits,
reproduction driver, and result explanations are written for this contribution.
Their proof scopes are stated in `README.md`; none claims an unrestricted
grammar lower bound, a fewer-than-245-state solution, or a newly completed
proof-assistant endpoint.

Related pairing-shift negation in ProveIt intakes 158/159 is credited in the
README. The present direct-retention identity and jointly changed physical
route are distinguished from that prior arithmetic simplification.
