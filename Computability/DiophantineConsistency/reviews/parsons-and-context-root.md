# Conjunction inversion inside an arbitrary context

`ParsonsAndContext.invert_below_exs` specializes the existing height-preserving
conjunction inversion to either conjunct of an occurrence at any position in
the nonprincipal context of an existential rule. It produces a cut-free
derivation strictly below the original existential conclusion without adding
permutation or contraction steps.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom report lists only `propext` and `Quot.sound`. The [16-file replay
manifest](parsons-and-context-replay/FILES.json) has SHA-256
`2faa576a6c60c43fcfbb07d9f609a6a59bbeb51e8f944686e9d4ed655ed96a41`.
The direct `ParsonsSelection` source hash
`2dbaf2b23983b72ee09f490f59413dff98be5bcdd271190a1ab5c6e25d471910`
matches the previously checked source, and the inherited object hash is
`1fd27ef4705f4c202aa136e3b27bf4a37a39fd1c3f28cfe41a4d9a75805ab0f1`.
Earlier providers and Foundation/Mathlib are an inherited boundary, not a
fresh transitive source audit.

The theorem is a source-side helper; it does not prove global recursion,
conservation, or the PRA-provability target. The separate HA theorem for the
maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-and-context-build-mh3cim4_`
passed with matching source, object and full-log hashes under the same
inherited-provider boundary.
