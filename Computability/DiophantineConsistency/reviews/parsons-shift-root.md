# Eigenvariable shift of a marked context

`ParsonsShift.normalized_closed` proves that the frozen parameter body has no
free variables. Consequently `state_shift` shifts the witness terms of any
partially opened induction block while retaining the original induction
formula and its state certificate. `Entry.shift` extends this to every marked
entry: Π₂ sides are shifted, PA-minus axioms remain closed, and special blocks
retain their shifted states. The mapped entry formulas and side contributions
are proved equal to the corresponding shifted sequents; the finite side
disjunction commutes with shifting as well.

`marked_universal` uses these results for the ordinary principal universal
rule with an **arbitrary marked nonprincipal context**. The entire context,
including special blocks and base axioms, is shifted coherently; the premise
is cut-free and strictly shorter than the original universal inference. Its
local recursive hypothesis remains explicit. This is stronger than treating
the remaining side as a single untracked formula, but it is not the global
induction.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Seven
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-shift-replay/FILES.json) has SHA-256
`4402be762ac2236c2aad0aeff5b73a33e9d49e273e276b18e3ccb64510314210`.
Direct `ParsonsInvariant` source/object hashes are
`39afa448679b7bc1b8f4d42b7d5a8611e9a9469172adaa3ca48eb3ce6d96f0be` /
`8686a84574be389aa2dc1a5ab2303812e27e967be61cf1cd9f8b9ed7a32a0fc4`;
`ParsonsLogicalCases` hashes are
`f00188fca71f773461419202fc212f99f036d42dc5ce6e171b6bb7f758266b68` /
`2695c7fcf17dcf3deb0758c2577277dcb60374adfec0ca5a5a1532db8fe525e5`.
Their inherited provider chain, Foundation/Mathlib, and completeness objects
are not freshly re-audited here. Scratch attempts involving the field
namespace and list-map simplification were fixed; their logs were not retained.

The global recursion still needs all other marked principal/nonprincipal
cases, especially extracting a Σ₁ guard from a general Π₂ side context for
the final induction-block case. No conservation or PRA witnessing theorem is
claimed.

## Independent root replay

A third build at `/tmp/parsons-shift-build-dij8okux` passed; source, object
and complete-log hashes match both author runs. The invariant and logical-case
providers match independently rebuilt objects. The [independent artifacts](parsons-shift-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
