# Exact inherited calibration interface

This note fixes the formal meaning of the ZFC consistency predicate used in the 238-state report. The new machine, its source correspondence, and its runtime proofs connect to an **inherited logical calibration** of `SourceRotation240.program` at `LogicalSeed246.initial`. This note records that inherited interface and the precise finite-proof and theory definitions behind it. It does not supply a new kernel proof of the binary endpoint or replace the full ancestor development.

All upstream citations below are pinned to ProveIt commit **`13ec39ed43148b1807f51ed6e6528e1c84659562`**. The small files in `calibration/*.excerpt.lean.txt` retain verbatim source ranges. They deliberately use a `.txt` extension: they are excerpts for review, not independently compilable Lean modules. Their original-file hashes, Git blob hashes, and exact line ranges are in [definition_excerpt_pins.json](calibration/definition_excerpt_pins.json). The inherited repository license is retained in `../licenses/LICENSE.ProveIt`.

## 1. Finite derivability from a theory

In the ancestor language, formulas are finite first-order syntax with equality and membership, using natural-number de Bruijn variable indices. `Prov G phi` is the inductively generated classical natural-deduction calculus from the finite context `G`. Its complete constructor declaration is:

```lean
inductive Prov : List Form → Form → Prop
  | P_ass    : ∀ G a, a ∈ G → Prov G a
  | P_impI   : ∀ G a b, Prov (a :: G) b → Prov G (fImp a b)
  | P_impE   : ∀ G a b, Prov G (fImp a b) → Prov G a → Prov G b
  | P_botE   : ∀ G a, Prov G fBot → Prov G a
  | P_lem    : ∀ G a, Prov G (fOr a (fImp a fBot))
  | P_andI   : ∀ G a b, Prov G a → Prov G b → Prov G (fAnd a b)
  | P_andE1  : ∀ G a b, Prov G (fAnd a b) → Prov G a
  | P_andE2  : ∀ G a b, Prov G (fAnd a b) → Prov G b
  | P_orI1   : ∀ G a b, Prov G a → Prov G (fOr a b)
  | P_orI2   : ∀ G a b, Prov G b → Prov G (fOr a b)
  | P_orE    : ∀ G a b c, Prov G (fOr a b) → Prov (a :: G) c → Prov (b :: G) c →
               Prov G c
  | P_allI   : ∀ G a, Prov (G.map (rename Nat.succ)) a → Prov G (fAll a)
  | P_allE   : ∀ G a k, Prov G (fAll a) → Prov G (rename (inst k) a)
  | P_exI    : ∀ G a k, Prov G (rename (inst k) a) → Prov G (fEx a)
  | P_exE    : ∀ G a c, Prov G (fEx a) →
               Prov (a :: G.map (rename Nat.succ)) (rename Nat.succ c) → Prov G c
  | P_eqRefl : ∀ G k, Prov G (fEq k k)
  /-- Proper Leibniz: from `i = j` and `a[0:=i]` infer `a[0:=j]` (`a` is the
  property with a hole at de Bruijn 0). Gives symmetry/transitivity/congruence. -/
  | P_eqElim : ∀ G i j a,
      Prov G (fEq i j) → Prov G (rename (inst i) a) → Prov G (rename (inst j) a)
```

Every constructor has finitely many derivation premises. An element of this inductive relation therefore has a finite derivation tree. The constructors include excluded middle, both quantifier introduction/elimination directions, equality reflexivity, and proper Leibniz substitution; this is the full retained calculus, not an equality-free fragment. [Source: Calculus.lean, lines 27–55][calculus]. A compact verbatim copy is [FirstOrderCalculus.Prov.excerpt.lean.txt](calibration/FirstOrderCalculus.Prov.excerpt.lean.txt).

For a possibly infinite theory predicate `B`, the ancestor then defines:

```lean
def BProv (B : Form → Prop) (G : List Form) (phi : Form) : Prop :=
  ∃ Gb, (∀ x ∈ Gb, B x) ∧ Prov (Gb ++ G) phi

def BCon (B : Form → Prop) (G : List Form) : Prop := ¬ BProv B G fBot
```

Thus `BProv B [] phi` means that there exists a **finite list of axioms of `B`** and a **finite `Prov` derivation from that list**. `BProv` itself is an existential definition; `Prov` is the inductive relation. In particular, the consistency assertion used at the inherited endpoint is `¬ BProv ZFCax_s [] fBot`. [Source: Completeness.lean, lines 307–311][completeness]. The exact excerpt is [FirstOrderCompleteness.BProv.excerpt.lean.txt](calibration/FirstOrderCompleteness.BProv.excerpt.lean.txt).

## 2. The retained first-order ZF theory

The exact sentence-theory predicate is:

```lean
def ZFax_s (f : Form) : Prop :=
  f = sealF Ext_form ∨ f = sealF Reg_form ∨ f = sealF Pow_form ∨
  f = sealF Pair_form ∨ f = sealF Union_form ∨ f = sealF Inf_form ∨
  (∃ phi, f = sealF (Sep_form phi)) ∨ (∃ psi, f = sealF (Repl_form psi))
```

Here `sealF` universally closes the free variables of a formula. The finite axioms are Extensionality, Foundation (`Reg_form`), Power Set, Pairing, Union, and Infinity. The remaining two disjuncts include all Separation instances and all functional Replacement instances, with formula parameters universally closed. The source formulas use explicit de Bruijn renamings to preserve the intended free parameters. [Source: Zf.lean, lines 40–57 and 101–140][zf]. Those renamings, all eight axiom constructors, and the theory definition are retained together in [ZF.Axioms.excerpt.lean.txt](calibration/ZF.Axioms.excerpt.lean.txt).

`Repl_form psi` uses global functionality of the relation defined by `psi`, followed by existence of its image on every set. This standard schema formulation is equivalent over the retained axioms to the usual set-restricted functional Replacement schema: restrict a relation to the given domain set, using that set as an additional parameter. The separate Empty Set axiom is redundant here; Infinity already asserts an empty member of an inductive set. Accordingly, the endpoint includes full ordinary ZF, including Foundation and Power Set.

## 3. The Choice axiom and the exact ZFC theory

The additional closed Choice sentence and its helper formulas are:

```lean
def Choice_nonempty : Form :=
  fAll (fImp (fMem 0 1) (fEx (fMem 0 1)))

def Choice_disjoint : Form :=
  fAll (fAll (fImp (fAnd (fAnd (fMem 1 2) (fMem 0 2)) (fNot (fEq 1 0)))
                   (fNot (fEx (fAnd (fMem 0 2) (fMem 0 1))))))

def Choice_selector : Form :=
  fAll (fImp (fMem 0 2)
          (fEx (fAnd (fAnd (fMem 0 1) (fMem 0 2))
                  (fAll (fImp (fAnd (fMem 0 2) (fMem 0 3)) (fEq 0 1))))))

def Choice_form : Form :=
  fAll (fImp (fAnd Choice_nonempty Choice_disjoint) (fEx Choice_selector))

def ZFCax_s (f : Form) : Prop := ZFax_s f ∨ f = sealF Choice_form
```

`Choice_form` says that every pairwise disjoint family of nonempty sets admits a set meeting every member in exactly one point. It is a **single closed axiom**, not a schema. The retained `Sentence_Choice_form` theorem checks closure, and `bridge_Choice` identifies the formula with its displayed semantic selector principle. It is sealed again in `ZFCax_s` to keep the sentence-theory presentation uniform. [Source: Choice.lean, lines 65–124 and 175–188][choice]. The relevant exact source is [ZFC.Choice.excerpt.lean.txt](calibration/ZFC.Choice.excerpt.lean.txt).

This is the standard selector formulation of Choice. Within ZF, a choice function yields such a selector by taking its range. Conversely, a family of arbitrary nonempty sets can be replaced by the disjoint family of tagged copies; a selector on those copies projects to a choice function. Consequently the displayed first-order sentence theory is an ordinary effective presentation of ZFC.

## 4. Identification with a natural-number proof predicate

The report's `Proof_ZFC(p, bot)` can be fixed concretely as a finite-code checker for:

1. A finite axiom list `Gb`, with a justification for each axiom.
2. A finite derivation tree using exactly the displayed `Prov` constructors and concluding `fBot` from `Gb`.

For a fixed axiom, its justification identifies the appropriate finite disjunct. For Separation or Replacement, its justification contains the finite witness formula `phi` or `psi`; the checker computes the corresponding axiom and its universal closure. Thus the existential schema presentation of `ZFax_s` creates no obstacle to effective finite checking. Variable renamings, formula equality, finite-list membership, and the derivation-rule checks are finite syntactic computations. This can be made an ordinary primitive-recursive proof predicate with conventional coding of finite syntax and trees.

Encoding and decoding give, in ordinary ZFC mathematics,

```text
BProv ZFCax_s [] fBot  <->  exists p, Proof_ZFC(p, bot).
```

For the forward direction, a finite axiom list uses only finitely many schema witnesses, and its `Prov` derivation is finite. For the reverse direction, each accepted code supplies precisely those witnesses and the corresponding inductive derivation. Ordinary changes among standard effective presentations of first-order ZFC use finite syntactic translations and preserve existence of a refutation. Negating the displayed equivalence identifies the endpoint with the corresponding `Con(ZFC)`.

This paragraph is an ordinary proof-coding argument. It is not a claim that this contribution has supplied a new Lean arithmetic proof-code interface or proved the complete statement internally in PA.

## 5. The exact inherited program endpoint

The retained [CalibratedRotation240.lean](calibration/CalibratedRotation240.lean) declares:

```lean
theorem halts_iff_zfc_refutation :
    RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_zfc_refutation
```

Its full upstream location is [Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CalibratedRotation240.lean][calibration]. The statement's program and initial state are concrete, not unspecified programs with equivalent consistency strength.

The exact seed in the retained [LogicalSeed246.lean](source_interface/LogicalSeed246.lean) is:

```lean
def seed : L2.AS := ⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩
def registers : RegisterPath.Registers := L2.enc seed
def initial : RegisterPath.Configuration := ⟨[], registers⟩
```

The same file proves the nine primary register values and `registers (i + 9) = 0`. Therefore the pointer is empty and the complete initial register function is `(3,0,0,0,3,0,0,0,0)`, followed by zeroes. [Upstream source][seed]. Auxiliary physical spare blocks in the binary runtime are not additional nonzero logical registers.

The inherited comparison passes through the following explicit interfaces:

| Interface | Mathematical role |
| --- | --- |
| `SourceRotation240.program_halts_iff`, then `CalibratedRotation244.program_halts_iff_original` | Relate the actual source to `Prog254.program` for the complete register function. |
| `LogicalSeed246.halts_iff_native_refutation` | Relate the exact seeded program to `BProv NativeAx [] fBot`. |
| `WFTheory.native_refutation_iff_zf` | Relate the native calculus to full `ZFax_s`, using the internally well-founded part of its CP/GIC quotient. |
| `ConstructibleChoice.zf_refutation_iff_zfc_refutation` | Relate ZF and ZFC refutations, using the constructible submodel and first-order soundness/completeness. |

The retained [WFTheory.lean](calibration/WFTheory.lean) and [ConstructibleChoice.lean](calibration/ConstructibleChoice.lean) show the two final theorem statements and their compositions. Their full transitive imports are inherited from the pinned ancestor, rather than reproduced in this archive. [Upstream WFTheory][wf]; [upstream ConstructibleChoice][constructible].

## 6. Scope of the new result

The new source-interface check identifies the full retained ordered source with the actual DAG definitions and overrides. The new source bisimulation preserves every instruction label, guarded successor index, and complete register function, including the exact seed. The blank-prefix and positive whole-tape runtime arguments provide the separate connection to the 238-state binary machine. The final theorem composes those new connections with the exact inherited calibration above and the ordinary proof-coding argument.

The source correspondence, finite transition proofs, and symbolic induction rules admit ordinary proofs in ZFC. The inherited model-theoretic arguments also use ordinary first-order syntax, models, quotients, and definable submodels. This statement of formalizability does not invoke a general soundness theorem for all of Lean's type theory within ZFC. The complete ancestor library was not rebuilt or independently re-proved during this contribution; no new Lean/Rocq binary endpoint or serialized ZFC derivation is claimed.

No consistency assumption is needed for the biconditional. Actual nonhalting follows under `Con(ZFC)`.

[calculus]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Logic/FirstOrder/Lean/FirstOrder/Calculus.lean#L27-L55
[completeness]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Logic/FirstOrder/Lean/FirstOrder/Completeness.lean#L307-L311
[zf]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/ZF/Lean/ZF/Zf.lean#L101-L140
[choice]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean#L65-L188
[calibration]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CalibratedRotation240.lean
[seed]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/LogicalSeed246.lean
[wf]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean
[constructible]: https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean
