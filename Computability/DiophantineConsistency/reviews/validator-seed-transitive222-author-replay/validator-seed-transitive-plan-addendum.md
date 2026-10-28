# Transitive proposal: profile-pair terminology correction

This source-only addendum preserves the frozen proposal and its four-file
manifest unchanged. It records the correction identified by
`complemented47_review` and independently checked against the literal sources.
No Lean source, cache, overlay or compiler was changed or executed.

The proposal `validator-seed-transitive-plan.md`, SHA256
`f4245ffeb787ba3c60da754dd1c6578b22d05e094622e0ae6b62052e3f33fb30`,
incorrectly describes the later `ProfilePairs.Pair` predicate in section 3
as involving interpreted Member and coded Eqv. The actual definitions are:

```text
Same mem x y := ∀ z, mem z x ↔ mem z y
ClassMember mem a b := ∃ z, mem z b ∧ Same mem a z
Pair mem p a b := ∀ z,
  ClassMember mem z p ↔ Same mem z a ∨ Same mem z b
```

Thus exact tagged raw pairs convert directly to the **Same/ClassMember**
profile-pair predicate, as `KLowerEqv.tag_pairs` shows. That conversion needs
neither coded Eqv laws nor the later Eqv-saturated interpreted Member.
Section 6's phrase “profile pairs” should be read with this precise meaning.

The proposed three source-proof endpoints, singleton/full-seed closure
argument, binder shapes, cache inventory and raw-code obligations are
unchanged. This correction does not add the profile-pair conversion to the
currently proposed implementation: it identifies the correct subsequent
source-certificate interface. Raw source equality, Same/ClassMember, coded
Eqv/Member and the actual validator Eind must remain distinct.

Source pins inspected for this correction:

| Source | SHA256 |
| --- | --- |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileCongruence.lean` (`Same`, line 15) | `a4a53a141352b87b3b6c8beb7b6376316c21aad5842ad62848407f586dca48ba` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfilePairs.lean` (`ClassMember`, line 21; `Pair`, line 28) | `d05b17aba8198b6c1fc5805d15fcb3353b5cf2bab07882942a489e4bc5637f9f` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerEqv.lean` (`tag_pairs`, line 44) | `0531258acfdd868577e1f23eaf5feb64441273472d762df3632601cada8f83e4` |

These are source-only anchors, not additional compiled dependencies. The
frozen proposed import remains solely `ZFCinPA.ValidatorSeedLogicalImages222`.
