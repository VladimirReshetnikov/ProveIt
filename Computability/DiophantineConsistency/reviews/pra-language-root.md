# Primitive-recursive first-order language: independent replay

29 October 2026. `PRALanguage` defines a first-order language whose functions
are finite primitive-recursive codes and whose relations are ordered-ring
identity and strict order. It designates concrete codes for zero, one,
addition and multiplication, and uses Foundation's ordered-ring language
embedding. Lean proves the arithmetic codes' natural semantics, equality of
the induced ordered-ring reduct with Foundation's standard natural structure,
and preservation of arbitrary ordered-ring formula semantics under the map.

I read both sources and independently rebuilt them with Lean 4.32,
`-M6000 -j1 -DElab.async=false`. Both objects and full logs match the author
build; four axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The [replay evidence](pra-language-root-replay/) includes all
six author attempts, final checks, the independent driver, state and logs.
The three earlier PRA code objects came from independently checked providers.
Foundation objects came from the reviewed hierarchy overlay and Mathlib
objects from the existing package cache; this is not an independent transitive
Foundation or Mathlib rebuild.

This is a language and standard-model interpretation, not yet a PRA axiom
system, proof predicate, proof of conservation, or PRA equivalence endpoint.
