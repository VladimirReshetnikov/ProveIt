# Complete ordinary high-mask safety for marked compact blocks

`CompactMarkedAllHigh.marked_all_high` proves in every model of IΣ₁ that each
physical normalized transport block of a marked compact word is `NoCarry`
against the entire symbolic high mask. Its assumptions are: Σ₁-definable
row and dummy functions, `CompactWord row N s`, `1<N`, `s<N`, and a dummy
function Boolean at **every model index**. There is no high-mask or complete
`PackingInput` assumption in this theorem.

The proof combines the separately checked exact phase classes: phase zero;
the vertical and horizontal field and marker intervals; the two distant
anchors; and the two occupied target phases. It uses the finite high-mask
support reduction and the previously proved vanishing padding tail, along
with the actual block size bound. The separate special-origin transfer is
still needed to replace the mask by `highNat - 1`; it requires `0<s<N` and
the already established origin-block residue.

This proves a key model-level packing condition for the exact **symbolic**
compact high mask. It does not by itself construct the remaining full
Diophantine graph witness, bind all retained/displayed coefficient bytes, or
prove an internal iPRA equivalence.

The guarded single-author mixed-provider run, session `7778`, exited 0
without warnings or `sorryAx`, with unchanged sampled direct-import,
companion, selected provider-root and overlay guards. Its named Lean axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The
complete provider overlap preflight, source/object hashes, command,
dependency listing, compiler log and terminal receipt are retained in
`observations/attempt01`. Package, transitive, dynamic and between-observation
ancestry remains inherited, and `/tmp` providers are ephemeral. This is not a
paired replay or independently authenticated complete closure.
