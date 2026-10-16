# First-order PSC calibration checked in Lean

`Lean/BusyBeaver/ZFC/PSCCalibration.lean` proves that Extensionality plus
the **subset-seeded**, subset-only positive closure schema has exactly the
same sentence theorems as ZF with Foundation and Choice omitted. The theorem
uses the repository's actual `SetTheory.Form`, finite-axiom `BProv` calculus,
and full first-order Separation and functional Replacement schemas.

The candidate sentence theory is `PSCAx`: the universal closure of
Extensionality, together with the universal closure of `pscForm phi` for
every formula `phi`. The comparison `ZF0Ax` has Extensionality, Pairing,
Union, Power Set and Infinity, plus the closed Separation and Replacement
instances. It adds neither Foundation, Choice nor a Collection schema.
Empty Set follows from its other axioms and the nonempty-domain convention.

The checked statements are:

```lean
psc_iff_zfAxioms :
  (Bootstrap.Extensional mem ∧ ModelsPSC mem) ↔
    (ZFAxioms mem ∧ PowerSets mem)

psc_iff_zf0 (phi : Form) (hSentence : Sentence phi) :
  BProv PSCAx [] phi ↔ BProv ZF0Ax [] phi

psc_consistency_iff_zf0 :
  (¬ BProv PSCAx [] fBot) ↔ (¬ BProv ZF0Ax [] fBot)
```

For the forward direction, `DefinableClosure.lean` supplies a concrete
formula and parameter environment for every relation used in the earlier
semantic bootstrap: exact constant fibers, the gated singleton decoder,
the two-cycle, the Russell-root image, and successor. All renamings are
checked under arbitrary binders in the inserted matrices. Thus the
conclusions use actual schema instances, not a closure axiom over every
external semantic relation.

For the reverse, local subset-boundedness of `rho(x,y)` makes its output
fiber membership-bounded by `P(b)` for a locally supplied bound `b`.
The existing `ZF.Zf.ClosureFO_of_ZF` closes a seed set `P(a)` under the
definable inverse relation. Its proof is internal to arbitrary first-order
models, using definable recursion; it assumes neither Foundation nor Power
Set. Here Power Set supplies the fiber bounds and initial seed set.
Separation turns the resulting closed superset `W` into
`C={y∈W : ∃x rho(x,y)}`. This removes unsupported members while retaining
all required outputs. Every formula and both relation orientations are
explicit in the checked argument.

The final `BProv` equivalence uses the existing generic first-order
completeness theorem. Its axiom audit is
`[propext, Classical.choice, Quot.sound]`, the ordinary Lean foundational
dependencies; it has no custom axioms, `sorry`, or native proof oracle.
The serial source-check command and source hashes are in
[results/lean-verification.json](results/lean-verification.json).

This is a calibrated control for compiler comparisons. An artificial theory
or proof calculus with a cheaper complete machine remains eligible. This
result does not calibrate the different fixed-binder **point-seeded** compiler
experiment or the raw variants without Extensionality/profile congruence.
It does not yet provide a computable proof-code translator, the separate
Foundation/Choice relative-consistency interpretations, or the final
ZFC-provable equivalence for a literal binary machine.
