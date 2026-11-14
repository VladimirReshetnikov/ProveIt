# Native iPRA proof of the fixed PA194 startup

`PA194StartupSentence.nativeIPRA` is a Lean-checked theorem of the native
intuitionistic PRA theory `IPRAStandardTheory.standardTheory` in the full
primitive-recursive function-code language, with intuitionistic first-order
logic, the defining equations and quantifier-free induction. Its closed equality says that the packed literal
PA194 stepper, started from the blank configuration, reaches the exact seed
frame after 58,154 steps. The result has dense state 24, left tape half 1, and
the right tape of `PA194StartupData.seedFrame`, including all 26 one-valued
spare blocks. Its input table is the pinned 194-state literal machine.

The step count and right tape value are represented by closed binary arithmetic
terms built from the actual 16-bit and 147-bit little-endian bit lists. Thus
neither the theorem statement nor its proof requires constructing a unary
numeral with the huge value of the right tape. The Lean code verifies the
clock's bit list and proves the binary terms denote their intended standard
numerals in every candidate PRA model.

The proof uses the independently kernel-checked literal dense startup trace,
the standard-input model bridge, classical PRA completeness, and the existing
negative-translation transfer to native iPRA. It does not establish the
subsequent source-frame simulation, any nonstandard-length execution property,
or either machine-specific consistency implication. In particular it does
not establish `iPRA ⊢ Con(PA) ↔ ¬Halt(M₁₉₄)`.

`modelSentence`, `classicalPRA`, and `nativeIPRA` were checked against the
retained prerequisite and dense-certificate overlays, and none of their printed
axiom dependencies includes `sorryAx`. A full run of `check-dense-startup.sh`
also regenerated and checked the literal startup certificate and rebuilt this
module; that run used the retained prerequisite overlays described in
[DENSE-STARTUP.md](DENSE-STARTUP.md).
