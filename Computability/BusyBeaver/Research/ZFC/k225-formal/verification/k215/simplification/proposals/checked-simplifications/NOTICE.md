# Attribution and scope

This packet is prepared for the ProveIt repository at commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`.

New report text, original proof/checker additions and synthesis code in this
packet are offered under the repository's MIT No Attribution license, reproduced
in `LICENSE`. This does not relicense any inherited third-party development.
Preserved notices and licenses in the component directories govern that material.

* **Normalized Rocq:** the 1,426-entry normalized relation and Lean implementation
  originate in incoming packet I2. The ordinary compact source checker, lossless
  path codec, plain mirror helper, compatibility module and dependency extraction
  originate in I5 and its cited upstream development. The new contribution is
  the proved normalized Rocq checker, exact source instance and interface adapter.
  See `normalized_rocq/PROVENANCE.json` and `normalized_rocq/licenses/`.
* **Decoder:** the finite 234-role product and 281-block framing proposal are
  prior incoming work (I4/I7). The exact frozen product JSON comes from I7.
  The arbitrary-tape Lean refinement, composition library, executable finite
  checker, literal instantiation and independently written audit are new here.
* **Zero credit:** command tags, codec and tag-lowering argument come from the
  repository's ZC215 work. The abstract finite-injection idea also appears in
  its earlier uncompiled `PrefixCredit.v`. The concrete codec/parser/inverse,
  lowering and all-prefix formalization in `TagLowering.v` is new here. Existing
  M124/FM215 machines and their incoming standalone transport proofs are not
  claimed as new; the exact comparison is supplied for disambiguation.
* **Search:** reference tables, the prior invariant-generator design and earlier
  search templates are attributed in `search214/NOTICE.md`. The coordinated
  temporary-tag/shared-selector family, simultaneous patch execution, independent
  invariant/control audit, and new bounded results are this packet's extension.

The numerical calculus, original compiler, parent Turing machines and existing
full ZFC endpoint remain the contributions of their original authors. The
archive supplies neither an unconditional nonhalting proof nor a new internal
arithmetization of proof-assistant soundness nor a verified 214-state candidate.
