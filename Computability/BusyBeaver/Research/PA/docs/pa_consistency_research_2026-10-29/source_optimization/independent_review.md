# Independent review of the 3,904-primitive source specialization

Reviewed `research/source_reduction/source_optimization/verify_source_optimization.py`, its generated source/CFG/projection, and `PROOF.md`. Independently executed the verifier under `python3 -O`, writing to `source_optimization_independent_replay/`. The result is `SOURCE_OPTIMIZATION_PASS`; regenerated hashes match the author's results:

- Original source: `cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
- Optimized source: `5c2ba0b336ea1e32921154a050c0231b5d1c45d440a7dd348ae39a57ef364f5d`.
- Zero/positive invariant: `f454cf5c9403613e81d27213aebfab472853ae6f2e3e6fbd3e3ee3753cff5d96`.

The two abstract transition relations are sound overapproximations of the specified natural-number counter semantics. The zero/positive domain allows both possible decrement results from a positive counter. The register-6 three-category domain distinguishes 0, 1, and at least 2; decrements of other counters are nondeterministic in both branches. Hence it does not assume a correlation with an untracked counter. Both finite families contain the initial abstraction and are checked for closure over every abstract successor.

The certificate proves the first deleted test at old ordinal 3847 has register 1 zero, with its positive-loop body 3848 and 3849 unreachable. The independent register-6 abstraction proves the second deleted test at 3891 has register 6 zero, and 3892 is unreachable. Both reachable removed tests take their zero edge without changing the register vector.

The revised checker additionally proves the first premise using only a single-register zero/positive abstraction, with 6,430 reachable pairs. I independently reran this revision under `python3 -O`; the result and source hashes remain unchanged. I separately enumerated every incoming edge to old ordinals 3837–3849: the only external entry is the zero exit of `CD 1` at 3834 to 3837. Instructions 3837–3846 affect only registers 5 and 6 or jump. Hence register 1 remains zero up to 3847; its positive body is impossible. This supports the shorter local proof and removes any need for nine-register correlations in the primary first-guard argument. The full 278,384-pair invariant remains useful auxiliary evidence.

The checker compares two complete source-CFG resolvers before and after modification. Every retained instruction has the same opcode and operand, and every outgoing edge is the exact projected old edge. Projection skips only 3847 to 3850 and 3891 to 3893. Each skip reaches a retained instruction immediately, so deleted reachable steps cannot support an infinite stuttering run. This is enough for a positive-block halting equivalence, with blocks of one or two old source steps per new step, from the stated seed. The seed remains at source ordinal 136 with the same address and instruction.

No semantic gap was found in this source-level argument. It is conditional on the stated source semantics and established initial seed, both explicitly identified by the author. It is an ordinary finite-certificate-and-induction proof, not an exported proof-assistant theorem. It does not allocate the new source to a smaller literal Turing table. Distinct source subtrees increase from 197 to 200, so primitive-occurrence savings alone do not imply physical state savings.
