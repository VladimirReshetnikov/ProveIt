# The remaining Foundation and Choice comparison

The CP/GIC quotient now has actual formula-indexed Separation and Replacement,
ordinary Infinity from the finite-attempt construction, and Power Set.
These resources target `PSCCalibration.ZF0Ax`, which omits Foundation and
Choice. Passing to full ZFC still requires relative-consistency proofs.
Adding a `ZFCAxioms` hypothesis to the quotient would assume the missing result.
This note records an independent source audit and exact open theorem targets;
it supplies no new Foundation/Choice proof or internal machine endpoint.

The existing presentations already give the required syntax:

| Presentation | Exact contents and source |
| --- | --- |
| `PSCCalibration.ZF0Ax` | Sealed Ext/Pow/Pair/Union/Inf and all Sep/Repl instances; [definition](../../Lean/BusyBeaver/ZFC/PSCCalibration.lean#L110), [model bridge](../../Lean/BusyBeaver/ZFC/PSCCalibration.lean#L136). |
| `SetTheory.ZFax_s` | The same sentences plus sealed `Reg_form`, with a different disjunction order; [definition](../../../../SetTheory/ZF/Lean/ZF/Zf.lean#L137), [Regularity bridge](../../../../SetTheory/ZF/Lean/ZF/Zf.lean#L182). |
| `LeanProofs.BoundedZFCConsistency.ZFCax_s` | `ZFax_s` plus sealed `Choice_form`; [definition](../../../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean#L188), [Choice bridge](../../../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean#L135). |

The repository's six-field `ZFAxioms` bundle itself omits both Power and
Regularity. `BoundedZFCConsistency.ZFCAxioms` adds Power, Regularity and Choice
as hypotheses; it is an axiom-extraction interface, not their relative
consistency theorem. The following two statements isolate the missing work
using the existing theories, without a stronger model assumption:

```lean
-- Targets only: these theorems have not been implemented.
regularity_refutation_remove :
  BProv SetTheory.ZFax_s [] Form.fBot →
  BProv PSCCalibration.ZF0Ax [] Form.fBot

choice_refutation_remove :
  BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot →
  BProv SetTheory.ZFax_s [] Form.fBot
```

Their composition would remove both extra axioms from a finite refutation.
The reverse implication follows from theory inclusion and the existing
`BProv_theory_mono`. Negating the two directions gives the consistency
comparison. Matching `ZFax_s` with `ZF0Ax` plus sealed Regularity needs only
propositional rearrangement of their definitions; it does not prove either
displayed target.

The pinned upstream source at
`297ab8df7e5de329605c3875b4934643b371a5e3` contains the relevant finite-proof
interpretations:

- The [well-founded-part formula](../../../../lib/jeff-busy-beaver-zfc254/ZF/stdzf_r3/regcon/WF.v#L209)
  and its axiom resources lead to
  [regularity_relcon](../../../../lib/jeff-busy-beaver-zfc254/ZF/stdzf_r3/regcon/Main.v#L432),
  then the closed-schema
  [regularity_relcon_std](../../../../lib/jeff-busy-beaver-zfc254/ZF/stdzf_r3/regcon/Link.v#L48).
- [ac_relcon](../../../../lib/jeff-busy-beaver-zfc254/ZF/stdzf_r3/zfc/Z_main.v#L38)
  relativizes a finite derivation to the definable constructible class. Its
  axiom and choice resources come from `Z_axL.v` and `Z_ac.v`.
- [ZFCReg_equicons](../../../../lib/jeff-busy-beaver-zfc254/ZF/stdzf_r3/zfc/Z_main.v#L83)
  is the combined comparison **including Foundation**. The nearby
  `ZFC_equicons` concerns ZF+AC with Foundation omitted; that name alone
  does not identify it with the repository's `ZFCax_s`.

Transport requires the actual language and schema conventions. Upstream uses
explicit equality axioms, closed schema instances and its own natural
deduction syntax; the local `Form` calculus has logical equality. The local
`Choice_form` is Zermelo's selector principle for pairwise disjoint nonempty
families. Its equivalence with choice-function presentations is stated but
not formalized in `Choice.lean`; matching upstream `ax_ac` requires this
object-theory comparison. Both are standard presentations of Choice, but
their finite proof translation is an explicit formal obligation.

A constructive Lean port can begin with literal `Form` relativization and
its proof transport, followed by the well-founded-part axiom resources and
then the constructible-class resources. Generic first-order completeness
does not supply those set-theoretic interpretations. A semantic alternative
must still build every actual interpreted Sep/Repl instance and an explicit
nonempty witness or valuation. External `WellFounded mem` is stronger than
object `Reg_form` in arbitrary nonstandard models; metatheoretic
`Classical.choice` does not construct an object selector set for an arbitrary
external family. Neither is a replacement for the displayed theorem targets.
The Cardinals constructibility interface assumes stronger indiscernible
machinery and includes an admitted input, so it is not this relative
consistency result.

The independent full read of `FiniteSets.lean` and `InductiveAttempts.lean`
found no circular Infinity premise, binder error or external-predicate
Separation assumption. Their graph constructors use only finite Pairing and
Union. Agreement and attempt existence use literal formula cuts. The
Replacement relation includes membership in the singleton index, so it is
globally partial-functional, including outside that index. The final quotient
uses the actual earlier schema interfaces and targets ordinary `Inf_form`.
This read-only audit performed no Lean or Coq build; source snapshots and
details are retained in `/tmp/zfc-infinity-independent-audit-wdtal64l/`.

The subsequent `QuotientZF0.lean` composition also reads clean: it fills all
six `ZFAxioms` fields, keeps Power separate, and applies `models_ZF0` to the
literal closed sentence theory. Its soundness corollary constructs a quotient
valuation from the raw witness. The decoded-bundle corollaries retain both IR
and an explicit valuation, whose slot0 supplies that witness. Their conclusion
is ordinary metatheoretic consistency of ZF0, with the two displayed
Foundation/Choice translations and the internal machine endpoint still open.
