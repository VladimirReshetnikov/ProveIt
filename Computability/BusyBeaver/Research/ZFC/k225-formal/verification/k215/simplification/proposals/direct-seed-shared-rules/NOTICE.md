# Attribution

This packet adapts the ProveIt source at commit
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95` for the proof-simplification request
of Vladimir Reshetnikov. Preserve the original repository's license and K215
attribution when integrating it.

The direct full-seed idea is explicitly described in the existing
`sharing-interfaces/calculus/DIRECT_FULL_SEED.md` proposal and implemented in
the existing Rocq `rocq224/src/Complete222.v`. This packet supplies its checked
Lean realization, exact interface-preserving source overlay, and validation.

The shared Rocq proof terms are inherited from Jeff Ketchersid's propositional
development and its ProveIt adaptation. Elliot Glazer's K-family calculus and
seed/model constructions remain their mathematical ancestry. The full Rocq
source identities and separate upstream notice are under `rocq/`.

The report and new scripts document the review, minimal-interface factoring,
fresh compilation evidence, measured source effects, remaining integration
requirements, and research questions. They do not claim the inherited
derivations or the direct-seed idea as newly discovered mathematical results.
