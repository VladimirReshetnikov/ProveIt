# Internal renaming and free-variable shift

`PA194RenameShiftCompatibility.lean` proves two term- and formula-level
compatibility results for the generic internal free-label renamer. If its
map parameters `p,q` satisfy `f p (x+1) = f q x + 1` at every model value `x`,
renaming `shift φ` at `p` equals shifting the renaming of `φ` at `q`. If they
satisfy `f p (x+1) = f q x`, renaming `shift φ` at `p` equals the renaming of
`φ` at `q`. Both results apply to arbitrary internally well-formed, including
nonstandard, terms and formulas.

The final three corollaries instantiate these identities for all branches of
`PA194ExpandedRename`: a positive protected prefix, a zero prefix and positive
exception index, and a zero prefix and zero exception index. The equations
hold for all model-valued labels, offsets, and flags. They connect the
index-level closure equations to actual Foundation internal formula syntax.

Results hold in every nonempty candidate-PRA model with equality and an IΣ₁
arithmetic reduct, assuming the generic renaming graph correctly represents
its map at every model value; the explicit expanded-family graph has that
correctness proved. Lean reports `propext`, `Classical.choice`, and `Quot.sound`
for the printed theorem dependencies, with no `sorryAx`.

The equalities do not yet transform finite formula contexts or internal
proofs. Substitution and eigenvariable compatibility, the other derivation
rules, and the full derivation transformer remain open; no iPRA consistency
implication is proved here.

Run `check-rename-shift-compatibility.sh` with the audited `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` set; it rebuilds dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed using the audited overlays, rebuilding
the local dependencies and finding no `sorryAx` in the displayed theorem axioms.
