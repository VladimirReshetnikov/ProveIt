import BoundedZFCConsistency.CodedDerivation
import BoundedZFCConsistency.Choice
import FirstOrder.ClassicalCompleteness

/-!
# Internal quantifier ranks on codes, the bounded-derivation predicate, and `Con_n`

`BoundedZFCConsistency.Basic` measures the quantifier complexity of a *external*
formula: `sigmaRank` and `piRank` are a mutual recursion on `Form`, and
`quantifierGroups` is their minimum.  `BoundedZFCConsistency.CodedDerivation`
codes derivations inside an arbitrary model of the `ZFAxioms` bundle and proves
them internally sound.  Between the two there is a gap that has to be closed
before the target sentence can even be written down: the rank has to exist *on
codes*, inside the model, as a `Form`-definable relation.

This file closes it, and then writes the sentence.

Neither Powerset nor Regularity is used.

## The internal ranks

The recursion is the one of `Basic`, read off the tag rather than off a parse
tree:

| tag | clause  | sigma                   | pi                      |
| --- | ------- | ----------------------- | ----------------------- |
| `0` | `fMem`  | `0`                     | `0`                     |
| `1` | `fEq`   | `0`                     | `0`                     |
| `2` | `fBot`  | `0`                     | `0`                     |
| `3` | `fImp`  | `max pa sb`             | `max sa pb`             |
| `4` | `fAnd`  | `max sa sb`             | `max pa pb`             |
| `5` | `fOr`   | `max sa sb`             | `max pa pb`             |
| `6` | `fAll`  | `(max 1 pa) + 1`        | `max 1 pa`              |
| `7` | `fEx`   | `max 1 sa`              | `(max 1 sa) + 1`        |

The two ranks refer to each other at the implication and at both quantifiers,
so they are carried as a *pair*: a rank triple is `⟨c, ⟨s, p⟩⟩`, which is the
shape of `satTriple`, and the object-language macro `fTripleMemF` reads it
unchanged.

Presentation is by certificates, exactly as for `Renames` in
`BoundedZFCConsistency.InternalSoundness`, and for the same reasons: the
intersection presentation would need a closed set to exist before its induction
principle said anything, while a certificate is a *set* of triples produced by
the induction itself.  Every clause strictly decreases the code, so closure
plus tag inversion pins the relation down and no rank on the certificate is
needed — unlike derivations, whose rules move in both directions.

`RankClosed` records internal naturality of both ranks, so `Ranks.mem_omega`
comes for free and the arithmetic of `ZF.Zf` applies to every rank, including
the nonstandard ones.

Totality and single-valuedness are proved by `isFormCodeSem_ind'`, so both hold
of nonstandard codes; and `ranks_formCode` identifies the internal ranks of a
quotation with the numerals of the metatheoretic ones.

## Internal maximum and the internal order

The clauses need `max` on the internal omega, which the ZF development does not
have.  Linearity of the internal omega — `nat_linear` of
`BoundedZFCConsistency.OmegaRecursion` — makes it a conditional definition,
`vmaxN H m n` being `n` when `m ∈ n` and `m` otherwise, and `vminN H m n` the
dual.  Internal `≤` is `LeN H m n`, membership in the successor, whose
disjunctive reading is `vsucc_spec`.

Both operators agree with the metatheoretic ones on numerals, which is what
turns the agreement statement for quotations into a statement about
`Nat.max`, `Nat.min` and `Nat.le`.

## The bound, and why it is an all-occurrences bound

`QuantBounded H b c` says that the smaller of the two internal ranks of `c` is
at most `b`.  It is the internal reading of `QuantifierBounded`, and
`quantBounded_formCode_iff` proves the two agree on quotations.

`DerAllBounded H b d` imposes the bound at *every* judgement recorded by the
derivation certificate: on the conclusion and on every member of the context.
That is strictly more than a conclusion-only bound — `fBot` has rank zero, so a
conclusion-only restriction is no restriction at all — but it is not obviously
the every-*occurrence* bound of `Basic.proofOccurrenceRank`, which also covers
the formula-valued rule parameters.  It is, and that is a theorem here rather
than a definition:

* every immediate subcode of a bounded code is bounded
  (`quantBounded_imp_left` and its six companions), because each rank of a
  compound dominates the corresponding rank of its parts on at least one
  polarity; and
* boundedness is invariant under internal renaming
  (`quantBounded_of_renames`), the internal counterpart of
  `Basic.hierarchyRanks_rename`.

Every formula a rule of the seventeen introduces as a parameter is an immediate
subcode of the conclusion of that node or of a cited premise — except the
Leibniz rule, whose parameter is a code of which the conclusion and the cited
premise are renamings.  `derStepBounded_of_derAllBounded` discharges all
seventeen, so `DerAllBounded` and the parameter-inclusive `DerStepBounded`
coincide on closed certificates.  Keeping the parameters out of the *definition*
is what keeps the object-language sentence small.

## The sentence assembled here is NOT `Con_n(ZFC)`

`logicConBodyF n` says: for the numeral of `n`, the empty context code and the
falsity code, no set is both a coded derivation of falsity from the empty
context and bounded at that numeral.  `logicConForm n` is its universal closure,
so sentencehood is `Sentence_seal` and no free-variable computation over a large
assembled formula is required.

The context is *empty*, so this is bounded consistency of **pure first-order
logic**, not of ZFC.  It is a genuine statement and its machinery is exactly
what the target needs, but it must not be mistaken for the target: `Con_n(ZFC)`
quantifies over derivations whose context consists of codes of ZFC axioms of
rank at most `n`, and expressing that needs an internal “codes a ZFC axiom”
predicate — one that recognizes the six fixed axioms by their quotations and the
Separation and Replacement schemas by an existential over the coded formula
constructors.  That predicate does not exist yet.

Indeed `logicConForm n` is already provable outright: `not_derives_bot` rules
out any coded derivation of falsity from the empty context as soon as the model
carries an internal set structure, and a trivial one always does.  The naming
here is deliberately honest about that.

`sat_logicConForm_iff` is the arbitrary-model characterization, relative to a
`ZFAxioms` bundle rather than to any particular model, and
`zfcprov_logicConForm_of_valid` is the endpoint bridge: by
`godel_completeness_for_theories`, truth in every model of `ZFCax_s` yields a
derivation from `ZFCax_s`.  That bridge is what the real `Con_n(ZFC)` will be
routed through once the axiom-code predicate and the corresponding sentence are
built.

## De Bruijn bookkeeping

Every macro carries a table of the slots it introduces.  Slot arguments named
`_i` are ABSOLUTE positions at the use site; each binder shifts the caller's
slots by one and the call sites account for the shift explicitly.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

/- The assembled formulas of this file — `logicConBodyF` in particular, which
contains `fDerivesF` and the whole rank rendering — are large terms, and the
elaborator recurses through them when it checks a definitional unfolding. -/
set_option maxRecDepth 8000

/- `sealF g` is `closeN (bound g) g`, so reducing it evaluates `bound` over the
whole of the formula being closed — for `logicConBodyF n` that is the entire coded
derivation predicate.  Nothing here needs to see through the closure operator,
and every fact used about it (`Sentence_seal`, `seal_valid`) is stated for an
arbitrary formula, so it is sealed off throughout. -/
attribute [local irreducible] SetTheory.sealF

universe u

section CodedRank

variable {V : Type u} {mem : V → V → Prop}

/-! ## The internal order, maximum and minimum

The von Neumann order is membership, so `≤` is membership in the successor.
`nat_linear` makes the two-element maximum and minimum definable by a
conditional; both are stated through their two defining equations rather than
through the conditional itself. -/

/-- Internal `≤` on the von Neumann naturals. -/
def LeN (H : ZFAxioms mem) (m n : V) : Prop := mem m (vsucc H n)

/-- The disjunctive reading of the internal order. -/
theorem leN_iff (H : ZFAxioms mem) (m n : V) :
    LeN H m n ↔ (mem m n ∨ m = n) := vsucc_spec H n m

theorem leN_of_mem (H : ZFAxioms mem) {m n : V} (h : mem m n) : LeN H m n :=
  (leN_iff H m n).mpr (Or.inl h)

theorem leN_refl (H : ZFAxioms mem) (m : V) : LeN H m m :=
  (leN_iff H m m).mpr (Or.inr rfl)

/-- Transitivity of the internal order.  Only the larger endpoint has to be an
internal natural, since that is the argument `nat_transitive` inspects. -/
theorem leN_trans (H : ZFAxioms mem) {x y z : V} (hz : mem z (omegaV H))
    (h1 : LeN H x y) (h2 : LeN H y z) : LeN H x z := by
  rcases (leN_iff H x y).mp h1 with h1 | rfl
  · rcases (leN_iff H y z).mp h2 with h2 | rfl
    · exact leN_of_mem H (nat_transitive H z hz y h2 x h1)
    · exact leN_of_mem H h1
  · exact h2

theorem vmaxN_exists (_H : ZFAxioms mem) (m n : V) :
    ∃ r, (mem m n → r = n) ∧ (¬ mem m n → r = m) := by
  rcases Classical.em (mem m n) with h | h
  · exact ⟨n, fun _ => rfl, fun h' => absurd h h'⟩
  · exact ⟨m, fun h' => absurd h' h, fun _ => rfl⟩

/-- The larger of two internal naturals. -/
noncomputable def vmaxN (H : ZFAxioms mem) (m n : V) : V :=
  (vmaxN_exists H m n).choose

theorem vmaxN_of_mem (H : ZFAxioms mem) {m n : V} (h : mem m n) :
    vmaxN H m n = n := (vmaxN_exists H m n).choose_spec.1 h

theorem vmaxN_of_not_mem (H : ZFAxioms mem) {m n : V} (h : ¬ mem m n) :
    vmaxN H m n = m := (vmaxN_exists H m n).choose_spec.2 h

theorem vminN_exists (_H : ZFAxioms mem) (m n : V) :
    ∃ r, (mem m n → r = m) ∧ (¬ mem m n → r = n) := by
  rcases Classical.em (mem m n) with h | h
  · exact ⟨m, fun _ => rfl, fun h' => absurd h h'⟩
  · exact ⟨n, fun h' => absurd h' h, fun _ => rfl⟩

/-- The smaller of two internal naturals. -/
noncomputable def vminN (H : ZFAxioms mem) (m n : V) : V :=
  (vminN_exists H m n).choose

theorem vminN_of_mem (H : ZFAxioms mem) {m n : V} (h : mem m n) :
    vminN H m n = m := (vminN_exists H m n).choose_spec.1 h

theorem vminN_of_not_mem (H : ZFAxioms mem) {m n : V} (h : ¬ mem m n) :
    vminN H m n = n := (vminN_exists H m n).choose_spec.2 h

theorem vmaxN_mem_omega (H : ZFAxioms mem) {m n : V} (hm : mem m (omegaV H))
    (hn : mem n (omegaV H)) : mem (vmaxN H m n) (omegaV H) := by
  rcases Classical.em (mem m n) with h | h
  · rw [vmaxN_of_mem H h]; exact hn
  · rw [vmaxN_of_not_mem H h]; exact hm

theorem vminN_mem_omega (H : ZFAxioms mem) {m n : V} (hm : mem m (omegaV H))
    (hn : mem n (omegaV H)) : mem (vminN H m n) (omegaV H) := by
  rcases Classical.em (mem m n) with h | h
  · rw [vminN_of_mem H h]; exact hm
  · rw [vminN_of_not_mem H h]; exact hn

theorem leN_vmaxN_left (H : ZFAxioms mem) {m n : V} (_hm : mem m (omegaV H))
    (_hn : mem n (omegaV H)) : LeN H m (vmaxN H m n) := by
  rcases Classical.em (mem m n) with h | h
  · rw [vmaxN_of_mem H h]; exact leN_of_mem H h
  · rw [vmaxN_of_not_mem H h]; exact leN_refl H m

theorem leN_vmaxN_right (H : ZFAxioms mem) {m n : V} (hm : mem m (omegaV H))
    (hn : mem n (omegaV H)) : LeN H n (vmaxN H m n) := by
  rcases Classical.em (mem m n) with h | h
  · rw [vmaxN_of_mem H h]; exact leN_refl H n
  · rw [vmaxN_of_not_mem H h]
    rcases nat_linear H n hn m hm with h' | h' | h'
    · exact leN_of_mem H h'
    · exact (leN_iff H n m).mpr (Or.inr h')
    · exact absurd h' h

theorem vminN_leN_left (H : ZFAxioms mem) {m n : V} (hm : mem m (omegaV H))
    (hn : mem n (omegaV H)) : LeN H (vminN H m n) m := by
  rcases Classical.em (mem m n) with h | h
  · rw [vminN_of_mem H h]; exact leN_refl H m
  · rw [vminN_of_not_mem H h]
    rcases nat_linear H n hn m hm with h' | h' | h'
    · exact leN_of_mem H h'
    · exact (leN_iff H n m).mpr (Or.inr h')
    · exact absurd h' h

theorem vminN_leN_right (H : ZFAxioms mem) {m n : V} (_hm : mem m (omegaV H))
    (_hn : mem n (omegaV H)) : LeN H (vminN H m n) n := by
  rcases Classical.em (mem m n) with h | h
  · rw [vminN_of_mem H h]; exact leN_of_mem H h
  · rw [vminN_of_not_mem H h]; exact leN_refl H n

/-- A common lower bound of two internal naturals is below their minimum. -/
theorem leN_vminN (H : ZFAxioms mem) {x m n : V} (h1 : LeN H x m)
    (h2 : LeN H x n) : LeN H x (vminN H m n) := by
  rcases Classical.em (mem m n) with h | h
  · rw [vminN_of_mem H h]; exact h1
  · rw [vminN_of_not_mem H h]; exact h2

/-! ### The order on numerals -/

/-- The internal order restricted to numerals is the external one.  The
forward direction is the only one needing an argument: a numeral cannot be a
member of a numeral of no larger external index, because that would put an
internal natural inside itself. -/
theorem natV_mem_iff (H : ZFAxioms mem) (j k : Nat) :
    mem (natV H j) (natV H k) ↔ j < k := by
  constructor
  · intro h
    rcases Nat.lt_or_ge j k with hjk | hkj
    · exact hjk
    · exfalso
      have h2 : mem (natV H j) (natV H j) := by
        rcases Nat.lt_or_ge k j with hk | hk
        · exact nat_transitive H (natV H j) (natV_mem_omega H j) (natV H k)
            (natV_lt H k j hk) (natV H j) h
        · have hkj' : k = j := Nat.le_antisymm hkj hk
          rw [hkj'] at h
          exact h
      exact nat_no_self H (natV H j) (natV_mem_omega H j) h2
  · exact natV_lt H j k

theorem leN_natV_iff (H : ZFAxioms mem) (j k : Nat) :
    LeN H (natV H j) (natV H k) ↔ j ≤ k := by
  rw [leN_iff]
  constructor
  · rintro (h | h)
    · exact Nat.le_of_lt ((natV_mem_iff H j k).mp h)
    · exact Nat.le_of_eq (natV_inj H j k h)
  · intro h
    rcases Nat.lt_or_ge j k with h' | h'
    · exact Or.inl ((natV_mem_iff H j k).mpr h')
    · exact Or.inr (by rw [Nat.le_antisymm h h'])

theorem vmaxN_natV (H : ZFAxioms mem) (j k : Nat) :
    vmaxN H (natV H j) (natV H k) = natV H (Nat.max j k) := by
  rcases Classical.em (mem (natV H j) (natV H k)) with h | h
  · have hjk : j < k := (natV_mem_iff H j k).mp h
    have hmax : Nat.max j k = k := by
      show max j k = k
      rw [Nat.max_def]
      split <;> omega
    rw [vmaxN_of_mem H h, hmax]
  · have hkj : k ≤ j := by
      rcases Nat.lt_or_ge j k with hlt | hge
      · exact absurd ((natV_mem_iff H j k).mpr hlt) h
      · exact hge
    have hmax : Nat.max j k = j := by
      show max j k = j
      rw [Nat.max_def]
      split <;> omega
    rw [vmaxN_of_not_mem H h, hmax]

theorem vminN_natV (H : ZFAxioms mem) (j k : Nat) :
    vminN H (natV H j) (natV H k) = natV H (Nat.min j k) := by
  rcases Classical.em (mem (natV H j) (natV H k)) with h | h
  · have hjk : j < k := (natV_mem_iff H j k).mp h
    have hmin : Nat.min j k = j := by
      show min j k = j
      rw [Nat.min_def]
      split <;> omega
    rw [vminN_of_mem H h, hmin]
  · have hkj : k ≤ j := by
      rcases Nat.lt_or_ge j k with hlt | hge
      · exact absurd ((natV_mem_iff H j k).mpr hlt) h
      · exact hge
    have hmin : Nat.min j k = k := by
      show min j k = k
      rw [Nat.min_def]
      split <;> omega
    rw [vminN_of_not_mem H h, hmin]

/-! ### The order and the two operators as `Form`s -/

/-- "slot `i` is at most slot `j`". -/
def fLeF (i j : Nat) : Form := fOr (fMem i j) (fEq i j)

theorem fLeF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j : Nat) :
    Sat mem ee (fLeF i j) ↔ LeN H (ee i) (ee j) :=
  (leN_iff H (ee i) (ee j)).symm

/-- "slot `i` is the larger of slots `j` and `k`". -/
def fMaxF (i j k : Nat) : Form :=
  fOr (fAnd (fMem j k) (fEq i k)) (fAnd (fImp (fMem j k) fBot) (fEq i j))

theorem fMaxF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k : Nat) :
    Sat mem ee (fMaxF i j k) ↔ ee i = vmaxN H (ee j) (ee k) := by
  show ((mem (ee j) (ee k) ∧ ee i = ee k) ∨
      ((mem (ee j) (ee k) → False) ∧ ee i = ee j)) ↔ _
  constructor
  · rintro (⟨h, he⟩ | ⟨h, he⟩)
    · rw [he, vmaxN_of_mem H h]
    · rw [he, vmaxN_of_not_mem H h]
  · intro h
    rcases Classical.em (mem (ee j) (ee k)) with hm | hm
    · exact Or.inl ⟨hm, by rw [h, vmaxN_of_mem H hm]⟩
    · exact Or.inr ⟨hm, by rw [h, vmaxN_of_not_mem H hm]⟩

/-- "slot `i` is the smaller of slots `j` and `k`". -/
def fMinF (i j k : Nat) : Form :=
  fOr (fAnd (fMem j k) (fEq i j)) (fAnd (fImp (fMem j k) fBot) (fEq i k))

theorem fMinF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k : Nat) :
    Sat mem ee (fMinF i j k) ↔ ee i = vminN H (ee j) (ee k) := by
  show ((mem (ee j) (ee k) ∧ ee i = ee j) ∨
      ((mem (ee j) (ee k) → False) ∧ ee i = ee k)) ↔ _
  constructor
  · rintro (⟨h, he⟩ | ⟨h, he⟩)
    · rw [he, vminN_of_mem H h]
    · rw [he, vminN_of_not_mem H h]
  · intro h
    rcases Classical.em (mem (ee j) (ee k)) with hm | hm
    · exact Or.inl ⟨hm, by rw [h, vminN_of_mem H hm]⟩
    · exact Or.inr ⟨hm, by rw [h, vminN_of_not_mem H hm]⟩

/-! ## The rank graph, by certificates

A rank triple is `⟨c, ⟨s, p⟩⟩`: a code, its sigma rank and its pi rank.  That
is the shape of `satTriple`, so the triple is written with `satTriple H c s p`
and `fTripleMemF` reads it unchanged.  The shape is shared with the evaluation
triples of `InternalSat`, the renaming triples of `InternalSoundness` and the
derivation triples of `CodedDerivation`; the meanings are not, and nothing
below mixes them. -/

/-- The triple `⟨c, s, p⟩` is justified by the rank triples recorded in `S`, by
one of the eight clauses of the module header.  Like `RenStep`, the relation is
*local*: it never mentions the rank relation, only membership in `S`. -/
def RankStep (H : ZFAxioms mem) (S c s p : V) : Prop :=
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 0) (kpair H i j) ∧
      s = natV H 0 ∧ p = natV H 0) ∨
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 1) (kpair H i j) ∧
      s = natV H 0 ∧ p = natV H 0) ∨
  (c = kpair H (natV H 2) (vempty H) ∧ s = natV H 0 ∧ p = natV H 0) ∨
  (∃ a b sa pa sb pb, c = kpair H (natV H 3) (kpair H a b) ∧
      mem (satTriple H a sa pa) S ∧ mem (satTriple H b sb pb) S ∧
      s = vmaxN H pa sb ∧ p = vmaxN H sa pb) ∨
  (∃ a b sa pa sb pb, c = kpair H (natV H 4) (kpair H a b) ∧
      mem (satTriple H a sa pa) S ∧ mem (satTriple H b sb pb) S ∧
      s = vmaxN H sa sb ∧ p = vmaxN H pa pb) ∨
  (∃ a b sa pa sb pb, c = kpair H (natV H 5) (kpair H a b) ∧
      mem (satTriple H a sa pa) S ∧ mem (satTriple H b sb pb) S ∧
      s = vmaxN H sa sb ∧ p = vmaxN H pa pb) ∨
  (∃ a sa pa, c = kpair H (natV H 6) a ∧
      mem (satTriple H a sa pa) S ∧
      s = vsucc H (vmaxN H (natV H 1) pa) ∧ p = vmaxN H (natV H 1) pa) ∨
  (∃ a sa pa, c = kpair H (natV H 7) a ∧
      mem (satTriple H a sa pa) S ∧
      s = vmaxN H (natV H 1) sa ∧ p = vsucc H (vmaxN H (natV H 1) sa))

/-- Every clause is positive in the set of established triples, so the step is
monotone.  This is what lets certificates be combined by union. -/
theorem rankStep_mono (H : ZFAxioms mem) {S S' c s p : V} (hsub : Sub mem S S')
    (h : RankStep H S c s p) : RankStep H S' c s p := by
  unfold RankStep at h ⊢
  rcases h with h | h | h | ⟨a, b, sa, pa, sb, pb, h1, m1, m2, h2, h3⟩ |
    ⟨a, b, sa, pa, sb, pb, h1, m1, m2, h2, h3⟩ |
    ⟨a, b, sa, pa, sb, pb, h1, m1, m2, h2, h3⟩ |
    ⟨a, sa, pa, h1, m1, h2, h3⟩ | ⟨a, sa, pa, h1, m1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, b, sa, pa, sb, pb, h1, hsub _ m1, hsub _ m2, h2, h3⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, b, sa, pa, sb, pb, h1, hsub _ m1, hsub _ m2, h2, h3⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, b, sa, pa, sb, pb, h1, hsub _ m1, hsub _ m2, h2, h3⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, sa, pa, h1, hsub _ m1, h2, h3⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨a, sa, pa, h1, hsub _ m1, h2, h3⟩))))))

/-- Every triple of `S` records two internal naturals and is justified by `S`.
Naturality is part of closure, rather than a separate induction, because the
`max` clauses need it at every recursive call. -/
def RankClosed (H : ZFAxioms mem) (S : V) : Prop :=
  ∀ c s p, mem (satTriple H c s p) S →
    (mem s (omegaV H) ∧ mem p (omegaV H) ∧ RankStep H S c s p)

theorem rankClosed_empty (H : ZFAxioms mem) : RankClosed H (vempty H) :=
  fun _ _ _ h => absurd h (vempty_spec H _)

theorem rankClosed_cup (H : ZFAxioms mem) {S1 S2 : V} (h1 : RankClosed H S1)
    (h2 : RankClosed H S2) : RankClosed H (vcup H S1 S2) := by
  intro c s p hmem
  rcases (vcup_spec H S1 S2 _).mp hmem with h | h
  · obtain ⟨hs, hp, hstep⟩ := h1 c s p h
    exact ⟨hs, hp, rankStep_mono H
      (fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inl hx)) hstep⟩
  · obtain ⟨hs, hp, hstep⟩ := h2 c s p h
    exact ⟨hs, hp, rankStep_mono H
      (fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inr hx)) hstep⟩

/-- Adjoining a single justified triple keeps a set closed.  As for renaming,
one new element always suffices: no clause quantifies over a carrier. -/
theorem rankClosed_insert (H : ZFAxioms mem) {S c s p : V}
    (hS : RankClosed H S) (hs : mem s (omegaV H)) (hp : mem p (omegaV H))
    (hstep : RankStep H S c s p) :
    RankClosed H (vcup H S (vsingle H (satTriple H c s p))) := by
  have hsub : Sub mem S (vcup H S (vsingle H (satTriple H c s p))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro d u v hmem
  rcases (vcup_spec H S (vsingle H (satTriple H c s p)) _).mp hmem with h | h
  · obtain ⟨h1, h2, h3⟩ := hS d u v h
    exact ⟨h1, h2, rankStep_mono H hsub h3⟩
  · obtain ⟨e1, e2, e3⟩ :=
      satTriple_inj H ((vsingle_spec H (satTriple H c s p) _).mp h)
    rw [e1, e2, e3]
    exact ⟨hs, hp, rankStep_mono H hsub hstep⟩

/-- `S` is a **rank certificate** for `⟨c, s, p⟩`. -/
structure RankCertifies (H : ZFAxioms mem) (S c s p : V) : Prop where
  /-- Every triple of the certificate is justified by the certificate. -/
  closed : RankClosed H S
  /-- The triple in question is recorded. -/
  holds : mem (satTriple H c s p) S

/-- **`s` and `p` are the internal sigma and pi ranks of the code `c`**: some
closed set records the triple. -/
def Ranks (H : ZFAxioms mem) (c s p : V) : Prop :=
  ∃ S, RankCertifies H S c s p

theorem Ranks.mem_omega (H : ZFAxioms mem) {c s p : V} (h : Ranks H c s p) :
    mem s (omegaV H) ∧ mem p (omegaV H) := by
  obtain ⟨S, hS, hmem⟩ := h
  exact ⟨(hS c s p hmem).1, (hS c s p hmem).2.1⟩

/-- A justified triple over a closed set can always be adjoined, which is the
only way the introduction rules below build certificates. -/
theorem ranks_of_step (H : ZFAxioms mem) {S c s p : V} (hS : RankClosed H S)
    (hs : mem s (omegaV H)) (hp : mem p (omegaV H))
    (hstep : RankStep H S c s p) : Ranks H c s p :=
  ⟨vcup H S (vsingle H (satTriple H c s p)),
    rankClosed_insert H hS hs hp hstep,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-! ### The introduction rules -/

theorem ranks_memAtom (H : ZFAxioms mem) {i j : V} (hi : mem i (omegaV H))
    (hj : mem j (omegaV H)) :
    Ranks H (kpair H (natV H 0) (kpair H i j)) (natV H 0) (natV H 0) := by
  refine ranks_of_step H (rankClosed_empty H) (natV_mem_omega H 0)
    (natV_mem_omega H 0) ?_
  unfold RankStep
  exact Or.inl ⟨i, j, hi, hj, rfl, rfl, rfl⟩

theorem ranks_eqAtom (H : ZFAxioms mem) {i j : V} (hi : mem i (omegaV H))
    (hj : mem j (omegaV H)) :
    Ranks H (kpair H (natV H 1) (kpair H i j)) (natV H 0) (natV H 0) := by
  refine ranks_of_step H (rankClosed_empty H) (natV_mem_omega H 0)
    (natV_mem_omega H 0) ?_
  unfold RankStep
  exact Or.inr (Or.inl ⟨i, j, hi, hj, rfl, rfl, rfl⟩)

theorem ranks_bot (H : ZFAxioms mem) :
    Ranks H (kpair H (natV H 2) (vempty H)) (natV H 0) (natV H 0) := by
  refine ranks_of_step H (rankClosed_empty H) (natV_mem_omega H 0)
    (natV_mem_omega H 0) ?_
  unfold RankStep
  exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

theorem ranks_imp (H : ZFAxioms mem) {a b sa pa sb pb : V}
    (h1 : Ranks H a sa pa) (h2 : Ranks H b sb pb) :
    Ranks H (kpair H (natV H 3) (kpair H a b))
      (vmaxN H pa sb) (vmaxN H sa pb) := by
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H h1
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H h2
  obtain ⟨S1, hS1, k1⟩ := h1
  obtain ⟨S2, hS2, k2⟩ := h2
  refine ranks_of_step H (rankClosed_cup H hS1 hS2)
    (vmaxN_mem_omega H hpa hsb) (vmaxN_mem_omega H hsa hpb) ?_
  unfold RankStep
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, sa, pa, sb, pb, rfl,
    (vcup_spec H S1 S2 _).mpr (Or.inl k1),
    (vcup_spec H S1 S2 _).mpr (Or.inr k2), rfl, rfl⟩)))

theorem ranks_and (H : ZFAxioms mem) {a b sa pa sb pb : V}
    (h1 : Ranks H a sa pa) (h2 : Ranks H b sb pb) :
    Ranks H (kpair H (natV H 4) (kpair H a b))
      (vmaxN H sa sb) (vmaxN H pa pb) := by
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H h1
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H h2
  obtain ⟨S1, hS1, k1⟩ := h1
  obtain ⟨S2, hS2, k2⟩ := h2
  refine ranks_of_step H (rankClosed_cup H hS1 hS2)
    (vmaxN_mem_omega H hsa hsb) (vmaxN_mem_omega H hpa hpb) ?_
  unfold RankStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨a, b, sa, pa, sb, pb, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl k1),
      (vcup_spec H S1 S2 _).mpr (Or.inr k2), rfl, rfl⟩))))

theorem ranks_or (H : ZFAxioms mem) {a b sa pa sb pb : V}
    (h1 : Ranks H a sa pa) (h2 : Ranks H b sb pb) :
    Ranks H (kpair H (natV H 5) (kpair H a b))
      (vmaxN H sa sb) (vmaxN H pa pb) := by
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H h1
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H h2
  obtain ⟨S1, hS1, k1⟩ := h1
  obtain ⟨S2, hS2, k2⟩ := h2
  refine ranks_of_step H (rankClosed_cup H hS1 hS2)
    (vmaxN_mem_omega H hsa hsb) (vmaxN_mem_omega H hpa hpb) ?_
  unfold RankStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨a, b, sa, pa, sb, pb, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl k1),
      (vcup_spec H S1 S2 _).mpr (Or.inr k2), rfl, rfl⟩)))))

theorem ranks_all (H : ZFAxioms mem) {a sa pa : V} (h : Ranks H a sa pa) :
    Ranks H (kpair H (natV H 6) a)
      (vsucc H (vmaxN H (natV H 1) pa)) (vmaxN H (natV H 1) pa) := by
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H h
  obtain ⟨S, hS, k⟩ := h
  have hm : mem (vmaxN H (natV H 1) pa) (omegaV H) :=
    vmaxN_mem_omega H (natV_mem_omega H 1) hpa
  refine ranks_of_step H hS (omega_succ H _ hm) hm ?_
  unfold RankStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨a, sa, pa, rfl, k, rfl, rfl⟩))))))

theorem ranks_ex (H : ZFAxioms mem) {a sa pa : V} (h : Ranks H a sa pa) :
    Ranks H (kpair H (natV H 7) a)
      (vmaxN H (natV H 1) sa) (vsucc H (vmaxN H (natV H 1) sa)) := by
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H h
  obtain ⟨S, hS, k⟩ := h
  have hm : mem (vmaxN H (natV H 1) sa) (omegaV H) :=
    vmaxN_mem_omega H (natV_mem_omega H 1) hsa
  refine ranks_of_step H hS hm (omega_succ H _ hm) ?_
  unfold RankStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨a, sa, pa, rfl, k, rfl, rfl⟩))))))

/-! ### Inverting the step at a known tag

Codes carrying different tags are different sets, so at a code of known shape
exactly one of the eight clauses can apply. -/

theorem rankStep_memAtom (H : ZFAxioms mem) {S i j s p : V}
    (h : RankStep H S (kpair H (natV H 0) (kpair H i j)) s p) :
    s = natV H 0 ∧ p = natV H 0 := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, _, hs, hp⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact ⟨hs, hp⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_eqAtom (H : ZFAxioms mem) {S i j s p : V}
    (h : RankStep H S (kpair H (natV H 1) (kpair H i j)) s p) :
    s = natV H 0 ∧ p = natV H 0 := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, _, hs, hp⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact ⟨hs, hp⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_bot (H : ZFAxioms mem) {S s p : V}
    (h : RankStep H S (kpair H (natV H 2) (vempty H)) s p) :
    s = natV H 0 ∧ p = natV H 0 := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨_, hs, hp⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact ⟨hs, hp⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_imp (H : ZFAxioms mem) {S a b s p : V}
    (h : RankStep H S (kpair H (natV H 3) (kpair H a b)) s p) :
    ∃ sa pa sb pb, mem (satTriple H a sa pa) S ∧
      mem (satTriple H b sb pb) S ∧
      s = vmaxN H pa sb ∧ p = vmaxN H sa pb := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨x, y, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hq⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hq
    refine ⟨sa, pa, sb, pb, ?_, ?_, hs, hp⟩
    · rw [h1]; exact m1
    · rw [h2]; exact m2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_and (H : ZFAxioms mem) {S a b s p : V}
    (h : RankStep H S (kpair H (natV H 4) (kpair H a b)) s p) :
    ∃ sa pa sb pb, mem (satTriple H a sa pa) S ∧
      mem (satTriple H b sb pb) S ∧
      s = vmaxN H sa sb ∧ p = vmaxN H pa pb := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨x, y, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hq⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hq
    refine ⟨sa, pa, sb, pb, ?_, ?_, hs, hp⟩
    · rw [h1]; exact m1
    · rw [h2]; exact m2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_or (H : ZFAxioms mem) {S a b s p : V}
    (h : RankStep H S (kpair H (natV H 5) (kpair H a b)) s p) :
    ∃ sa pa sb pb, mem (satTriple H a sa pa) S ∧
      mem (satTriple H b sb pb) S ∧
      s = vmaxN H sa sb ∧ p = vmaxN H pa pb := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨x, y, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hq⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hq
    refine ⟨sa, pa, sb, pb, ?_, ?_, hs, hp⟩
    · rw [h1]; exact m1
    · rw [h2]; exact m2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_all (H : ZFAxioms mem) {S a s p : V}
    (h : RankStep H S (kpair H (natV H 6) a) s p) :
    ∃ sa pa, mem (satTriple H a sa pa) S ∧
      s = vsucc H (vmaxN H (natV H 1) pa) ∧ p = vmaxN H (natV H 1) pa := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨x, sa, pa, hc, m1, hs, hp⟩ |
    ⟨_, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    exact ⟨sa, pa, by rw [h1]; exact m1, hs, hp⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem rankStep_ex (H : ZFAxioms mem) {S a s p : V}
    (h : RankStep H S (kpair H (natV H 7) a) s p) :
    ∃ sa pa, mem (satTriple H a sa pa) S ∧
      s = vmaxN H (natV H 1) sa ∧ p = vsucc H (vmaxN H (natV H 1) sa) := by
  unfold RankStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, hc, _, _, _, _⟩ | ⟨_, _, _, hc, _, _, _⟩ |
    ⟨x, sa, pa, hc, m1, hs, hp⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    exact ⟨sa, pa, by rw [h1]; exact m1, hs, hp⟩

/-! ### The inversion rules for `Ranks` -/

theorem ranks_memAtom_inv (H : ZFAxioms mem) {i j s p : V}
    (h : Ranks H (kpair H (natV H 0) (kpair H i j)) s p) :
    s = natV H 0 ∧ p = natV H 0 := by
  obtain ⟨S, hS, hmem⟩ := h
  exact rankStep_memAtom H (hS _ _ _ hmem).2.2

theorem ranks_eqAtom_inv (H : ZFAxioms mem) {i j s p : V}
    (h : Ranks H (kpair H (natV H 1) (kpair H i j)) s p) :
    s = natV H 0 ∧ p = natV H 0 := by
  obtain ⟨S, hS, hmem⟩ := h
  exact rankStep_eqAtom H (hS _ _ _ hmem).2.2

theorem ranks_bot_inv (H : ZFAxioms mem) {s p : V}
    (h : Ranks H (kpair H (natV H 2) (vempty H)) s p) :
    s = natV H 0 ∧ p = natV H 0 := by
  obtain ⟨S, hS, hmem⟩ := h
  exact rankStep_bot H (hS _ _ _ hmem).2.2

theorem ranks_imp_inv (H : ZFAxioms mem) {a b s p : V}
    (h : Ranks H (kpair H (natV H 3) (kpair H a b)) s p) :
    ∃ sa pa sb pb, Ranks H a sa pa ∧ Ranks H b sb pb ∧
      s = vmaxN H pa sb ∧ p = vmaxN H sa pb := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨sa, pa, sb, pb, m1, m2, hs, hp⟩ := rankStep_imp H (hS _ _ _ hmem).2.2
  exact ⟨sa, pa, sb, pb, ⟨S, hS, m1⟩, ⟨S, hS, m2⟩, hs, hp⟩

theorem ranks_and_inv (H : ZFAxioms mem) {a b s p : V}
    (h : Ranks H (kpair H (natV H 4) (kpair H a b)) s p) :
    ∃ sa pa sb pb, Ranks H a sa pa ∧ Ranks H b sb pb ∧
      s = vmaxN H sa sb ∧ p = vmaxN H pa pb := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨sa, pa, sb, pb, m1, m2, hs, hp⟩ := rankStep_and H (hS _ _ _ hmem).2.2
  exact ⟨sa, pa, sb, pb, ⟨S, hS, m1⟩, ⟨S, hS, m2⟩, hs, hp⟩

theorem ranks_or_inv (H : ZFAxioms mem) {a b s p : V}
    (h : Ranks H (kpair H (natV H 5) (kpair H a b)) s p) :
    ∃ sa pa sb pb, Ranks H a sa pa ∧ Ranks H b sb pb ∧
      s = vmaxN H sa sb ∧ p = vmaxN H pa pb := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨sa, pa, sb, pb, m1, m2, hs, hp⟩ := rankStep_or H (hS _ _ _ hmem).2.2
  exact ⟨sa, pa, sb, pb, ⟨S, hS, m1⟩, ⟨S, hS, m2⟩, hs, hp⟩

theorem ranks_all_inv (H : ZFAxioms mem) {a s p : V}
    (h : Ranks H (kpair H (natV H 6) a) s p) :
    ∃ sa pa, Ranks H a sa pa ∧
      s = vsucc H (vmaxN H (natV H 1) pa) ∧ p = vmaxN H (natV H 1) pa := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨sa, pa, m1, hs, hp⟩ := rankStep_all H (hS _ _ _ hmem).2.2
  exact ⟨sa, pa, ⟨S, hS, m1⟩, hs, hp⟩

theorem ranks_ex_inv (H : ZFAxioms mem) {a s p : V}
    (h : Ranks H (kpair H (natV H 7) a) s p) :
    ∃ sa pa, Ranks H a sa pa ∧
      s = vmaxN H (natV H 1) sa ∧ p = vsucc H (vmaxN H (natV H 1) sa) := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨sa, pa, m1, hs, hp⟩ := rankStep_ex H (hS _ _ _ hmem).2.2
  exact ⟨sa, pa, ⟨S, hS, m1⟩, hs, hp⟩

/-! ## The rank relation as a `Form`

Everything from here on has to be readable inside the object language, because
`isFormCodeSem_ind'` takes its property as a formula with parameters. -/

/-- An atomic rank clause with tag `t`: both ranks are zero.

| de Bruijn slot | contents                   |
| -------------- | -------------------------- |
| `0`            | the second index `j`       |
| `1`            | the first index `i`        |
| `m+2`          | the caller's slot `m`      |
-/
def fRankAtomF (c_i s_i p_i t : Nat) : Form :=
  fEx (fEx (fAnd (fNatF 1) (fAnd (fNatF 0)
    (fAnd (fTagPairF (c_i+2) t 1 0)
      (fAnd (fNumF (s_i+2) 0) (fNumF (p_i+2) 0))))))

theorem fRankAtomF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i t : Nat) :
    Sat mem ee (fRankAtomF c_i s_i p_i t) ↔
      ∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
        ee c_i = kpair H (natV H t) (kpair H i j) ∧
        ee s_i = natV H 0 ∧ ee p_i = natV H 0 := by
  constructor
  · rintro ⟨i, j, hi, hj, hc, hs, hp⟩
    exact ⟨i, j, (fNatF_spec H _ 1).mp hi, (fNatF_spec H _ 0).mp hj,
      (fTagPairF_spec H _ (c_i+2) t 1 0).mp hc,
      (fNumF_spec H 0 (s_i+2) _).mp hs, (fNumF_spec H 0 (p_i+2) _).mp hp⟩
  · rintro ⟨i, j, hi, hj, hc, hs, hp⟩
    exact ⟨i, j, (fNatF_spec H _ 1).mpr hi, (fNatF_spec H _ 0).mpr hj,
      (fTagPairF_spec H _ (c_i+2) t 1 0).mpr hc,
      (fNumF_spec H 0 (s_i+2) _).mpr hs, (fNumF_spec H 0 (p_i+2) _).mpr hp⟩

/-- The falsity rank clause: both ranks are zero. -/
def fRankBotF (c_i s_i p_i : Nat) : Form :=
  fAnd (fTaggedEmptyF c_i 2) (fAnd (fNumF s_i 0) (fNumF p_i 0))

theorem fRankBotF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i : Nat) :
    Sat mem ee (fRankBotF c_i s_i p_i) ↔
      (ee c_i = kpair H (natV H 2) (vempty H) ∧
        ee s_i = natV H 0 ∧ ee p_i = natV H 0) :=
  and_congr (fTaggedEmptyF_spec H ee c_i 2)
    (and_congr (fNumF_spec H 0 s_i ee) (fNumF_spec H 0 p_i ee))

/-- The implication rank clause, where the antecedent changes polarity.

| de Bruijn slot | contents                   |
| -------------- | -------------------------- |
| `0`            | the pi rank `pb` of `b`    |
| `1`            | the sigma rank `sb` of `b` |
| `2`            | the pi rank `pa` of `a`    |
| `3`            | the sigma rank `sa` of `a` |
| `4`            | the second subcode `b`     |
| `5`            | the first subcode `a`      |
| `m+6`          | the caller's slot `m`      |
-/
def fRankImpF (c_i s_i p_i r_i : Nat) : Form :=
  fEx (fEx (fEx (fEx (fEx (fEx
    (fAnd (fTagPairF (c_i+6) 3 5 4)
      (fAnd (fTripleMemF 5 3 2 (r_i+6))
        (fAnd (fTripleMemF 4 1 0 (r_i+6))
          (fAnd (fMaxF (s_i+6) 2 1) (fMaxF (p_i+6) 3 0))))))))))

theorem fRankImpF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i r_i : Nat) :
    Sat mem ee (fRankImpF c_i s_i p_i r_i) ↔
      ∃ a b sa pa sb pb, ee c_i = kpair H (natV H 3) (kpair H a b) ∧
        mem (satTriple H a sa pa) (ee r_i) ∧
        mem (satTriple H b sb pb) (ee r_i) ∧
        ee s_i = vmaxN H pa sb ∧ ee p_i = vmaxN H sa pb := by
  constructor
  · rintro ⟨a, b, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩
    exact ⟨a, b, sa, pa, sb, pb,
      (fTagPairF_spec H _ (c_i+6) 3 5 4).mp hc,
      (fTripleMemF_spec H _ 5 3 2 (r_i+6)).mp m1,
      (fTripleMemF_spec H _ 4 1 0 (r_i+6)).mp m2,
      (fMaxF_spec H _ (s_i+6) 2 1).mp hs, (fMaxF_spec H _ (p_i+6) 3 0).mp hp⟩
  · rintro ⟨a, b, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩
    exact ⟨a, b, sa, pa, sb, pb,
      (fTagPairF_spec H _ (c_i+6) 3 5 4).mpr hc,
      (fTripleMemF_spec H _ 5 3 2 (r_i+6)).mpr m1,
      (fTripleMemF_spec H _ 4 1 0 (r_i+6)).mpr m2,
      (fMaxF_spec H _ (s_i+6) 2 1).mpr hs, (fMaxF_spec H _ (p_i+6) 3 0).mpr hp⟩

/-- A componentwise-maximum rank clause with tag `t`, for conjunction and
disjunction.  The slot table is that of `fRankImpF`. -/
def fRankBinF (c_i s_i p_i r_i t : Nat) : Form :=
  fEx (fEx (fEx (fEx (fEx (fEx
    (fAnd (fTagPairF (c_i+6) t 5 4)
      (fAnd (fTripleMemF 5 3 2 (r_i+6))
        (fAnd (fTripleMemF 4 1 0 (r_i+6))
          (fAnd (fMaxF (s_i+6) 3 1) (fMaxF (p_i+6) 2 0))))))))))

theorem fRankBinF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i s_i p_i r_i t : Nat) :
    Sat mem ee (fRankBinF c_i s_i p_i r_i t) ↔
      ∃ a b sa pa sb pb, ee c_i = kpair H (natV H t) (kpair H a b) ∧
        mem (satTriple H a sa pa) (ee r_i) ∧
        mem (satTriple H b sb pb) (ee r_i) ∧
        ee s_i = vmaxN H sa sb ∧ ee p_i = vmaxN H pa pb := by
  constructor
  · rintro ⟨a, b, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩
    exact ⟨a, b, sa, pa, sb, pb,
      (fTagPairF_spec H _ (c_i+6) t 5 4).mp hc,
      (fTripleMemF_spec H _ 5 3 2 (r_i+6)).mp m1,
      (fTripleMemF_spec H _ 4 1 0 (r_i+6)).mp m2,
      (fMaxF_spec H _ (s_i+6) 3 1).mp hs, (fMaxF_spec H _ (p_i+6) 2 0).mp hp⟩
  · rintro ⟨a, b, sa, pa, sb, pb, hc, m1, m2, hs, hp⟩
    exact ⟨a, b, sa, pa, sb, pb,
      (fTagPairF_spec H _ (c_i+6) t 5 4).mpr hc,
      (fTripleMemF_spec H _ 5 3 2 (r_i+6)).mpr m1,
      (fTripleMemF_spec H _ 4 1 0 (r_i+6)).mpr m2,
      (fMaxF_spec H _ (s_i+6) 3 1).mpr hs, (fMaxF_spec H _ (p_i+6) 2 0).mpr hp⟩

/-- The universal rank clause: the pi rank is preserved and the sigma rank
costs one.

| de Bruijn slot | contents                        |
| -------------- | ------------------------------- |
| `0`            | the intermediate `max 1 pa`     |
| `1`            | the numeral `1`                 |
| `2`            | the pi rank `pa` of the body    |
| `3`            | the sigma rank `sa` of the body |
| `4`            | the body `a`                    |
| `m+5`          | the caller's slot `m`           |
-/
def fRankAllF (c_i s_i p_i r_i : Nat) : Form :=
  fEx (fEx (fEx (fEx (fEx
    (fAnd (fTagUnF (c_i+5) 6 4)
      (fAnd (fTripleMemF 4 3 2 (r_i+5))
        (fAnd (fNumF 1 1)
          (fAnd (fMaxF 0 1 2)
            (fAnd (fSuccF (s_i+5) 0) (fEq (p_i+5) 0))))))))))

theorem fRankAllF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i r_i : Nat) :
    Sat mem ee (fRankAllF c_i s_i p_i r_i) ↔
      ∃ a sa pa, ee c_i = kpair H (natV H 6) a ∧
        mem (satTriple H a sa pa) (ee r_i) ∧
        ee s_i = vsucc H (vmaxN H (natV H 1) pa) ∧
        ee p_i = vmaxN H (natV H 1) pa := by
  constructor
  · rintro ⟨a, sa, pa, one, m, hc, hm, hone, hmax, hs, hp⟩
    have hone' : one = natV H 1 := (fNumF_spec H 1 1 _).mp hone
    have hmax' : m = vmaxN H one pa := (fMaxF_spec H _ 0 1 2).mp hmax
    rw [hone'] at hmax'
    refine ⟨a, sa, pa, (fTagUnF_spec H _ (c_i+5) 6 4).mp hc,
      (fTripleMemF_spec H _ 4 3 2 (r_i+5)).mp hm, ?_, ?_⟩
    · have hs' : ee s_i = vsucc H m := (fSuccF_spec H _ (s_i+5) 0).mp hs
      rw [hs', hmax']
    · show ee p_i = _
      have hp' : ee p_i = m := hp
      rw [hp', hmax']
  · rintro ⟨a, sa, pa, hc, hm, hs, hp⟩
    refine ⟨a, sa, pa, natV H 1, vmaxN H (natV H 1) pa,
      (fTagUnF_spec H _ (c_i+5) 6 4).mpr hc,
      (fTripleMemF_spec H _ 4 3 2 (r_i+5)).mpr hm,
      (fNumF_spec H 1 1 _).mpr rfl,
      (fMaxF_spec H _ 0 1 2).mpr rfl,
      (fSuccF_spec H _ (s_i+5) 0).mpr hs, hp⟩

/-- The existential rank clause, dual to `fRankAllF`. -/
def fRankExF (c_i s_i p_i r_i : Nat) : Form :=
  fEx (fEx (fEx (fEx (fEx
    (fAnd (fTagUnF (c_i+5) 7 4)
      (fAnd (fTripleMemF 4 3 2 (r_i+5))
        (fAnd (fNumF 1 1)
          (fAnd (fMaxF 0 1 3)
            (fAnd (fEq (s_i+5) 0) (fSuccF (p_i+5) 0))))))))))

theorem fRankExF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i r_i : Nat) :
    Sat mem ee (fRankExF c_i s_i p_i r_i) ↔
      ∃ a sa pa, ee c_i = kpair H (natV H 7) a ∧
        mem (satTriple H a sa pa) (ee r_i) ∧
        ee s_i = vmaxN H (natV H 1) sa ∧
        ee p_i = vsucc H (vmaxN H (natV H 1) sa) := by
  constructor
  · rintro ⟨a, sa, pa, one, m, hc, hm, hone, hmax, hs, hp⟩
    have hone' : one = natV H 1 := (fNumF_spec H 1 1 _).mp hone
    have hmax' : m = vmaxN H one sa := (fMaxF_spec H _ 0 1 3).mp hmax
    rw [hone'] at hmax'
    refine ⟨a, sa, pa, (fTagUnF_spec H _ (c_i+5) 7 4).mp hc,
      (fTripleMemF_spec H _ 4 3 2 (r_i+5)).mp hm, ?_, ?_⟩
    · show ee s_i = _
      have hs' : ee s_i = m := hs
      rw [hs', hmax']
    · have hp' : ee p_i = vsucc H m := (fSuccF_spec H _ (p_i+5) 0).mp hp
      rw [hp', hmax']
  · rintro ⟨a, sa, pa, hc, hm, hs, hp⟩
    refine ⟨a, sa, pa, natV H 1, vmaxN H (natV H 1) sa,
      (fTagUnF_spec H _ (c_i+5) 7 4).mpr hc,
      (fTripleMemF_spec H _ 4 3 2 (r_i+5)).mpr hm,
      (fNumF_spec H 1 1 _).mpr rfl,
      (fMaxF_spec H _ 0 1 3).mpr rfl,
      hs, (fSuccF_spec H _ (p_i+5) 0).mpr hp⟩

/-- "the triple ⟨slot `c_i`, slot `s_i`, slot `p_i`⟩ is justified by slot
`r_i`" — the eight clauses of `RankStep`, in the order of the module header. -/
def fRankStepF (c_i s_i p_i r_i : Nat) : Form :=
  fOr (fRankAtomF c_i s_i p_i 0)
   (fOr (fRankAtomF c_i s_i p_i 1)
    (fOr (fRankBotF c_i s_i p_i)
     (fOr (fRankImpF c_i s_i p_i r_i)
      (fOr (fRankBinF c_i s_i p_i r_i 4)
       (fOr (fRankBinF c_i s_i p_i r_i 5)
        (fOr (fRankAllF c_i s_i p_i r_i)
             (fRankExF c_i s_i p_i r_i)))))))

theorem fRankStepF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i r_i : Nat) :
    Sat mem ee (fRankStepF c_i s_i p_i r_i) ↔
      RankStep H (ee r_i) (ee c_i) (ee s_i) (ee p_i) := by
  unfold RankStep
  exact or_congr (fRankAtomF_spec H ee c_i s_i p_i 0)
    (or_congr (fRankAtomF_spec H ee c_i s_i p_i 1)
      (or_congr (fRankBotF_spec H ee c_i s_i p_i)
        (or_congr (fRankImpF_spec H ee c_i s_i p_i r_i)
          (or_congr (fRankBinF_spec H ee c_i s_i p_i r_i 4)
            (or_congr (fRankBinF_spec H ee c_i s_i p_i r_i 5)
              (or_congr (fRankAllF_spec H ee c_i s_i p_i r_i)
                        (fRankExF_spec H ee c_i s_i p_i r_i)))))))

/-- "slot `r_i` is closed under the rank step".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the pi rank `p`         |
| `1`            | the sigma rank `s`      |
| `2`            | the code `c`            |
| `m+3`          | the caller's slot `m`   |
-/
def fRankClosedF (r_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (r_i+3))
    (fAnd (fNatF 1) (fAnd (fNatF 0) (fRankStepF 2 1 0 (r_i+3)))))))

theorem fRankClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i : Nat) :
    Sat mem ee (fRankClosedF r_i) ↔ RankClosed H (ee r_i) := by
  unfold RankClosed
  constructor
  · intro h c s p hmem
    obtain ⟨h1, h2, h3⟩ := h c s p
      ((fTripleMemF_spec H _ 2 1 0 (r_i+3)).mpr hmem)
    exact ⟨(fNatF_spec H _ 1).mp h1, (fNatF_spec H _ 0).mp h2,
      (fRankStepF_spec H _ 2 1 0 (r_i+3)).mp h3⟩
  · intro h c s p hsat
    obtain ⟨h1, h2, h3⟩ := h c s p
      ((fTripleMemF_spec H _ 2 1 0 (r_i+3)).mp hsat)
    exact ⟨(fNatF_spec H _ 1).mpr h1, (fNatF_spec H _ 0).mpr h2,
      (fRankStepF_spec H _ 2 1 0 (r_i+3)).mpr h3⟩

/-- "slots `s_i` and `p_i` are the internal ranks of slot `c_i`".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the certificate `S`     |
| `m+1`          | the caller's slot `m`   |
-/
def fRanksF (c_i s_i p_i : Nat) : Form :=
  fEx (fAnd (fRankClosedF 0) (fTripleMemF (c_i+1) (s_i+1) (p_i+1) 0))

theorem fRanksF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i s_i p_i : Nat) :
    Sat mem ee (fRanksF c_i s_i p_i) ↔
      Ranks H (ee c_i) (ee s_i) (ee p_i) := by
  constructor
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fRankClosedF_spec H (scons S ee) 0).mp hS,
      (fTripleMemF_spec H (scons S ee) (c_i+1) (s_i+1) (p_i+1) 0).mp hmem⟩
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fRankClosedF_spec H (scons S ee) 0).mpr hS,
      (fTripleMemF_spec H (scons S ee) (c_i+1) (s_i+1) (p_i+1) 0).mpr hmem⟩

/-! ## Totality and single-valuedness -/

/-- Every code has a pair of internal ranks. -/
def RankTotal (H : ZFAxioms mem) (c : V) : Prop :=
  ∃ s p, Ranks H c s p

/-- `RankTotal` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents             |
| -------------- | -------------------- |
| `0`            | the pi rank `p`      |
| `1`            | the sigma rank `s`   |
| `2`            | the code `c`         |
-/
def fRankTotalF : Form := fEx (fEx (fRanksF 2 1 0))

theorem fRankTotalF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (fun _ => vempty H)) fRankTotalF ↔ RankTotal H y := by
  unfold RankTotal
  constructor
  · rintro ⟨s, p, h⟩
    exact ⟨s, p, (fRanksF_spec H _ 2 1 0).mp h⟩
  · rintro ⟨s, p, h⟩
    exact ⟨s, p, (fRanksF_spec H _ 2 1 0).mpr h⟩

/-- **The internal ranks are total.**  Every code — including the nonstandard
ones — carries a pair of ranks.  The atomic and falsity cases start from the
empty certificate; the compound cases union the certificates supplied by the
induction hypothesis and adjoin one new triple. -/
theorem rankTotal_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → RankTotal H c := by
  refine isFormCodeSem_ind' H (RankTotal H) fRankTotalF (fun _ => vempty H)
    (fun y => (fRankTotalF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun i j hi hj => ⟨_, _, ranks_memAtom H hi hj⟩
  · exact fun i j hi hj => ⟨_, _, ranks_eqAtom H hi hj⟩
  · exact ⟨_, _, ranks_bot H⟩
  · rintro a b ⟨sa, pa, ha⟩ ⟨sb, pb, hb⟩
    exact ⟨_, _, ranks_imp H ha hb⟩
  · rintro a b ⟨sa, pa, ha⟩ ⟨sb, pb, hb⟩
    exact ⟨_, _, ranks_and H ha hb⟩
  · rintro a b ⟨sa, pa, ha⟩ ⟨sb, pb, hb⟩
    exact ⟨_, _, ranks_or H ha hb⟩
  · rintro a ⟨sa, pa, ha⟩
    exact ⟨_, _, ranks_all H ha⟩
  · rintro a ⟨sa, pa, ha⟩
    exact ⟨_, _, ranks_ex H ha⟩

/-- A code determines both of its ranks. -/
def RankUnique (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ s1 p1 s2 p2, Ranks H c s1 p1 → Ranks H c s2 p2 → s1 = s2 ∧ p1 = p2

/-- `RankUnique` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                  |
| -------------- | ------------------------- |
| `0`            | the second pi rank `p2`   |
| `1`            | the second sigma rank `s2`|
| `2`            | the first pi rank `p1`    |
| `3`            | the first sigma rank `s1` |
| `4`            | the code `c`              |
-/
def fRankUniqueF : Form :=
  fAll (fAll (fAll (fAll (fImp (fRanksF 4 3 2)
    (fImp (fRanksF 4 1 0) (fAnd (fEq 3 1) (fEq 2 0)))))))

theorem fRankUniqueF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (fun _ => vempty H)) fRankUniqueF ↔ RankUnique H y := by
  unfold RankUnique
  constructor
  · intro h s1 p1 s2 p2 h1 h2
    exact h s1 p1 s2 p2 ((fRanksF_spec H _ 4 3 2).mpr h1)
      ((fRanksF_spec H _ 4 1 0).mpr h2)
  · intro h s1 p1 s2 p2 h1 h2
    exact h s1 p1 s2 p2 ((fRanksF_spec H _ 4 3 2).mp h1)
      ((fRanksF_spec H _ 4 1 0).mp h2)

/-- **The internal ranks are single-valued.**  Each case inverts both
hypotheses at the known tag and either reads off the same closed term or
applies the induction hypothesis to the subcodes. -/
theorem rankUnique_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → RankUnique H c := by
  refine isFormCodeSem_ind' H (RankUnique H) fRankUniqueF (fun _ => vempty H)
    (fun y => (fRankUniqueF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ s1 p1 s2 p2 h1 h2
    obtain ⟨e1, e2⟩ := ranks_memAtom_inv H h1
    obtain ⟨e3, e4⟩ := ranks_memAtom_inv H h2
    exact ⟨by rw [e1, e3], by rw [e2, e4]⟩
  · intro _ _ _ _ s1 p1 s2 p2 h1 h2
    obtain ⟨e1, e2⟩ := ranks_eqAtom_inv H h1
    obtain ⟨e3, e4⟩ := ranks_eqAtom_inv H h2
    exact ⟨by rw [e1, e3], by rw [e2, e4]⟩
  · intro s1 p1 s2 p2 h1 h2
    obtain ⟨e1, e2⟩ := ranks_bot_inv H h1
    obtain ⟨e3, e4⟩ := ranks_bot_inv H h2
    exact ⟨by rw [e1, e3], by rw [e2, e4]⟩
  · intro a b ha hb s1 p1 s2 p2 h1 h2
    obtain ⟨sa1, pa1, sb1, pb1, k1, l1, e1, e2⟩ := ranks_imp_inv H h1
    obtain ⟨sa2, pa2, sb2, pb2, k2, l2, e3, e4⟩ := ranks_imp_inv H h2
    obtain ⟨ea1, ea2⟩ := ha sa1 pa1 sa2 pa2 k1 k2
    obtain ⟨eb1, eb2⟩ := hb sb1 pb1 sb2 pb2 l1 l2
    exact ⟨by rw [e1, e3, ea2, eb1], by rw [e2, e4, ea1, eb2]⟩
  · intro a b ha hb s1 p1 s2 p2 h1 h2
    obtain ⟨sa1, pa1, sb1, pb1, k1, l1, e1, e2⟩ := ranks_and_inv H h1
    obtain ⟨sa2, pa2, sb2, pb2, k2, l2, e3, e4⟩ := ranks_and_inv H h2
    obtain ⟨ea1, ea2⟩ := ha sa1 pa1 sa2 pa2 k1 k2
    obtain ⟨eb1, eb2⟩ := hb sb1 pb1 sb2 pb2 l1 l2
    exact ⟨by rw [e1, e3, ea1, eb1], by rw [e2, e4, ea2, eb2]⟩
  · intro a b ha hb s1 p1 s2 p2 h1 h2
    obtain ⟨sa1, pa1, sb1, pb1, k1, l1, e1, e2⟩ := ranks_or_inv H h1
    obtain ⟨sa2, pa2, sb2, pb2, k2, l2, e3, e4⟩ := ranks_or_inv H h2
    obtain ⟨ea1, ea2⟩ := ha sa1 pa1 sa2 pa2 k1 k2
    obtain ⟨eb1, eb2⟩ := hb sb1 pb1 sb2 pb2 l1 l2
    exact ⟨by rw [e1, e3, ea1, eb1], by rw [e2, e4, ea2, eb2]⟩
  · intro a ha s1 p1 s2 p2 h1 h2
    obtain ⟨sa1, pa1, k1, e1, e2⟩ := ranks_all_inv H h1
    obtain ⟨sa2, pa2, k2, e3, e4⟩ := ranks_all_inv H h2
    obtain ⟨ea1, ea2⟩ := ha sa1 pa1 sa2 pa2 k1 k2
    exact ⟨by rw [e1, e3, ea2], by rw [e2, e4, ea2]⟩
  · intro a ha s1 p1 s2 p2 h1 h2
    obtain ⟨sa1, pa1, k1, e1, e2⟩ := ranks_ex_inv H h1
    obtain ⟨sa2, pa2, k2, e3, e4⟩ := ranks_ex_inv H h2
    obtain ⟨ea1, ea2⟩ := ha sa1 pa1 sa2 pa2 k1 k2
    exact ⟨by rw [e1, e3, ea1], by rw [e2, e4, ea1]⟩

/-! ## Agreement with the metatheoretic ranks on quotations

The internal ranks of a quoted formula are the numerals of `sigmaRank` and
`piRank`.  The induction is on the external parse tree; `vmaxN_natV` is what
turns each internal clause into its metatheoretic counterpart. -/

/-- **Quotation soundness for the ranks.** -/
theorem ranks_formCode (H : ZFAxioms mem) (phi : Form) :
    Ranks H (formCode H phi) (natV H (sigmaRank phi)) (natV H (piRank phi)) := by
  induction phi with
  | fMem i j =>
      exact ranks_memAtom H (natV_mem_omega H i) (natV_mem_omega H j)
  | fEq i j =>
      exact ranks_eqAtom H (natV_mem_omega H i) (natV_mem_omega H j)
  | fBot => exact ranks_bot H
  | fImp a b iha ihb =>
      have h := ranks_imp H iha ihb
      rw [vmaxN_natV, vmaxN_natV] at h
      exact h
  | fAnd a b iha ihb =>
      have h := ranks_and H iha ihb
      rw [vmaxN_natV, vmaxN_natV] at h
      exact h
  | fOr a b iha ihb =>
      have h := ranks_or H iha ihb
      rw [vmaxN_natV, vmaxN_natV] at h
      exact h
  | fAll a ih =>
      have h := ranks_all H ih
      rw [show natV H 1 = natV H 1 from rfl, vmaxN_natV] at h
      exact h
  | fEx a ih =>
      have h := ranks_ex H ih
      rw [show natV H 1 = natV H 1 from rfl, vmaxN_natV] at h
      exact h

/-- The internal ranks of a quotation are exactly the numerals of the
metatheoretic ranks: single-valuedness turns the previous theorem into a
determination. -/
theorem ranks_formCode_iff (H : ZFAxioms mem) (phi : Form) (s p : V) :
    Ranks H (formCode H phi) s p ↔
      (s = natV H (sigmaRank phi) ∧ p = natV H (piRank phi)) := by
  constructor
  · intro h
    obtain ⟨e1, e2⟩ :=
      rankUnique_of_isFormCodeSem H _ (formCode_isFormCodeSem H phi)
        s p _ _ h (ranks_formCode H phi)
    exact ⟨e1, e2⟩
  · rintro ⟨rfl, rfl⟩
    exact ranks_formCode H phi

/-! ## The bound on codes -/

/-- **The code `c` has quantifier complexity at most `b`**: the smaller of its
two internal ranks is below the internal bound.  This is the internal reading
of `QuantifierBounded`. -/
def QuantBounded (H : ZFAxioms mem) (b c : V) : Prop :=
  ∃ s p, Ranks H c s p ∧ LeN H (vminN H s p) b

/-- `QuantBounded` as a `Form`.

| de Bruijn slot | contents                  |
| -------------- | ------------------------- |
| `0`            | the minimum of the ranks  |
| `1`            | the pi rank `p`           |
| `2`            | the sigma rank `s`        |
| `m+3`          | the caller's slot `m`     |
-/
def fQuantBoundedF (b_i c_i : Nat) : Form :=
  fEx (fEx (fEx (fAnd (fRanksF (c_i+3) 2 1)
    (fAnd (fMinF 0 2 1) (fLeF 0 (b_i+3))))))

theorem fQuantBoundedF_spec (H : ZFAxioms mem) (ee : Nat → V) (b_i c_i : Nat) :
    Sat mem ee (fQuantBoundedF b_i c_i) ↔
      QuantBounded H (ee b_i) (ee c_i) := by
  unfold QuantBounded
  constructor
  · rintro ⟨s, p, m, hr, hm, hle⟩
    refine ⟨s, p, (fRanksF_spec H _ (c_i+3) 2 1).mp hr, ?_⟩
    have hm' : m = vminN H s p := (fMinF_spec H _ 0 2 1).mp hm
    have hle' := (fLeF_spec H _ 0 (b_i+3)).mp hle
    rw [hm'] at hle'
    exact hle'
  · rintro ⟨s, p, hr, hle⟩
    exact ⟨s, p, vminN H s p, (fRanksF_spec H _ (c_i+3) 2 1).mpr hr,
      (fMinF_spec H _ 0 2 1).mpr rfl, (fLeF_spec H _ 0 (b_i+3)).mpr hle⟩

/-- On quotations the internal bound is the metatheoretic one. -/
theorem quantBounded_formCode_iff (H : ZFAxioms mem) (n : Nat) (phi : Form) :
    QuantBounded H (natV H n) (formCode H phi) ↔ QuantifierBounded n phi := by
  unfold QuantBounded QuantifierBounded quantifierGroups
  constructor
  · rintro ⟨s, p, hr, hle⟩
    obtain ⟨rfl, rfl⟩ := (ranks_formCode_iff H phi s p).mp hr
    rw [vminN_natV, leN_natV_iff] at hle
    exact hle
  · intro h
    refine ⟨natV H (sigmaRank phi), natV H (piRank phi),
      ranks_formCode H phi, ?_⟩
    rw [vminN_natV, leN_natV_iff]
    exact h

/-! ### Boundedness descends to the subcodes

Each rank of a compound dominates, on at least one polarity, each rank of each
part, so the minimum of a part is below the minimum of the whole.  This is what
makes the node bound of a coded derivation an every-occurrence bound. -/

/-- A common upper bound for both ranks of a code bounds the code. -/
theorem quantBounded_of_le (H : ZFAxioms mem) {b c s p x : V}
    (hr : Ranks H c s p) (h1 : LeN H (vminN H s p) x)
    (hx : mem b (omegaV H)) (h2 : LeN H x b) : QuantBounded H b c :=
  ⟨s, p, hr, leN_trans H hx h1 h2⟩

theorem quantBounded_imp (H : ZFAxioms mem) {b a a' : V}
    (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 3) (kpair H a a'))) :
    QuantBounded H b a ∧ QuantBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_imp_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hs
  subst hp
  constructor
  · refine ⟨sa, pa, ha, leN_trans H hb (leN_vminN H ?_ ?_) hle⟩
    · exact leN_trans H (vmaxN_mem_omega H hpa hsb) (vminN_leN_right H hsa hpa)
        (leN_vmaxN_left H hpa hsb)
    · exact leN_trans H (vmaxN_mem_omega H hsa hpb) (vminN_leN_left H hsa hpa)
        (leN_vmaxN_left H hsa hpb)
  · refine ⟨sb, pb, hb', leN_trans H hb (leN_vminN H ?_ ?_) hle⟩
    · exact leN_trans H (vmaxN_mem_omega H hpa hsb) (vminN_leN_left H hsb hpb)
        (leN_vmaxN_right H hpa hsb)
    · exact leN_trans H (vmaxN_mem_omega H hsa hpb) (vminN_leN_right H hsb hpb)
        (leN_vmaxN_right H hsa hpb)

theorem quantBounded_and (H : ZFAxioms mem) {b a a' : V}
    (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 4) (kpair H a a'))) :
    QuantBounded H b a ∧ QuantBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_and_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hs
  subst hp
  constructor
  · refine ⟨sa, pa, ha, leN_trans H hb ?_ hle⟩
    exact leN_vminN H
      (leN_trans H (vmaxN_mem_omega H hsa hsb) (vminN_leN_left H hsa hpa)
        (leN_vmaxN_left H hsa hsb))
      (leN_trans H (vmaxN_mem_omega H hpa hpb) (vminN_leN_right H hsa hpa)
        (leN_vmaxN_left H hpa hpb))
  · refine ⟨sb, pb, hb', leN_trans H hb ?_ hle⟩
    exact leN_vminN H
      (leN_trans H (vmaxN_mem_omega H hsa hsb) (vminN_leN_left H hsb hpb)
        (leN_vmaxN_right H hsa hsb))
      (leN_trans H (vmaxN_mem_omega H hpa hpb) (vminN_leN_right H hsb hpb)
        (leN_vmaxN_right H hpa hpb))

theorem quantBounded_or (H : ZFAxioms mem) {b a a' : V}
    (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 5) (kpair H a a'))) :
    QuantBounded H b a ∧ QuantBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_or_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hs
  subst hp
  constructor
  · refine ⟨sa, pa, ha, leN_trans H hb ?_ hle⟩
    exact leN_vminN H
      (leN_trans H (vmaxN_mem_omega H hsa hsb) (vminN_leN_left H hsa hpa)
        (leN_vmaxN_left H hsa hsb))
      (leN_trans H (vmaxN_mem_omega H hpa hpb) (vminN_leN_right H hsa hpa)
        (leN_vmaxN_left H hpa hpb))
  · refine ⟨sb, pb, hb', leN_trans H hb ?_ hle⟩
    exact leN_vminN H
      (leN_trans H (vmaxN_mem_omega H hsa hsb) (vminN_leN_left H hsb hpb)
        (leN_vmaxN_right H hsa hsb))
      (leN_trans H (vmaxN_mem_omega H hpa hpb) (vminN_leN_right H hsb hpb)
        (leN_vmaxN_right H hpa hpb))

theorem quantBounded_all (H : ZFAxioms mem) {b a : V} (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 6) a)) : QuantBounded H b a := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_all_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  have hm : mem (vmaxN H (natV H 1) pa) (omegaV H) :=
    vmaxN_mem_omega H (natV_mem_omega H 1) hpa
  subst hs
  subst hp
  have hB : LeN H (vminN H sa pa) (vmaxN H (natV H 1) pa) :=
    leN_trans H hm (vminN_leN_right H hsa hpa)
      (leN_vmaxN_right H (natV_mem_omega H 1) hpa)
  refine ⟨sa, pa, ha, leN_trans H hb (leN_vminN H ?_ hB) hle⟩
  exact leN_trans H (omega_succ H _ hm) hB (leN_of_mem H (vsucc_self H _))

theorem quantBounded_ex (H : ZFAxioms mem) {b a : V} (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 7) a)) : QuantBounded H b a := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_ex_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  have hm : mem (vmaxN H (natV H 1) sa) (omegaV H) :=
    vmaxN_mem_omega H (natV_mem_omega H 1) hsa
  subst hs
  subst hp
  have hA : LeN H (vminN H sa pa) (vmaxN H (natV H 1) sa) :=
    leN_trans H hm (vminN_leN_left H hsa hpa)
      (leN_vmaxN_right H (natV_mem_omega H 1) hsa)
  refine ⟨sa, pa, ha, leN_trans H hb (leN_vminN H hA ?_) hle⟩
  exact leN_trans H (omega_succ H _ hm) hA (leN_of_mem H (vsucc_self H _))

/-! ### Boundedness is invariant under internal renaming

The internal counterpart of `Basic.hierarchyRanks_rename`.  A renaming changes
the variable indices of a code and nothing else, so it changes neither rank. -/

/-- Every renaming of the code carries the same ranks. -/
def RankRen (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ r c' s p, IsVarMap H r → Renames H r c c' → Ranks H c s p → Ranks H c' s p

/-- `RankRen` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents               |
| -------------- | ---------------------- |
| `0`            | the pi rank `p`        |
| `1`            | the sigma rank `s`     |
| `2`            | the renaming `c'`      |
| `3`            | the variable map `r`   |
| `4`            | the code `c`           |
-/
def fRankRenF : Form :=
  fAll (fAll (fAll (fAll (fImp (fVarMapF 3)
    (fImp (fRenamesF 3 4 2) (fImp (fRanksF 4 1 0) (fRanksF 2 1 0)))))))

theorem fRankRenF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (fun _ => vempty H)) fRankRenF ↔ RankRen H y := by
  unfold RankRen
  constructor
  · intro h r c' s p hr hren hrk
    exact (fRanksF_spec H _ 2 1 0).mp
      (h r c' s p ((fVarMapF_spec H _ 3).mpr hr)
        ((fRenamesF_spec H _ 3 4 2).mpr hren)
        ((fRanksF_spec H _ 4 1 0).mpr hrk))
  · intro h r c' s p hr hren hrk
    exact (fRanksF_spec H _ 2 1 0).mpr
      (h r c' s p ((fVarMapF_spec H _ 3).mp hr)
        ((fRenamesF_spec H _ 3 4 2).mp hren)
        ((fRanksF_spec H _ 4 1 0).mp hrk))

theorem rankRen_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → RankRen H c := by
  refine isFormCodeSem_ind' H (RankRen H) fRankRenF (fun _ => vempty H)
    (fun y => (fRankRenF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj r c' s p hr hren hrk
    obtain ⟨e1, e2⟩ := ranks_memAtom_inv H hrk
    rw [renames_memAtom_inv H hren, e1, e2]
    exact ranks_memAtom H (isVarMap_apply H hr hi) (isVarMap_apply H hr hj)
  · intro i j hi hj r c' s p hr hren hrk
    obtain ⟨e1, e2⟩ := ranks_eqAtom_inv H hrk
    rw [renames_eqAtom_inv H hren, e1, e2]
    exact ranks_eqAtom H (isVarMap_apply H hr hi) (isVarMap_apply H hr hj)
  · intro r c' s p _ hren hrk
    obtain ⟨e1, e2⟩ := ranks_bot_inv H hrk
    rw [renames_bot_inv H hren, e1, e2]
    exact ranks_bot H
  · intro a b ha hb r c' s p hr hren hrk
    obtain ⟨a', b', hc', k1, k2⟩ := renames_imp_inv H hren
    obtain ⟨sa, pa, sb, pb, ra, rb, hs, hp⟩ := ranks_imp_inv H hrk
    rw [hc', hs, hp]
    exact ranks_imp H (ha r a' sa pa hr k1 ra) (hb r b' sb pb hr k2 rb)
  · intro a b ha hb r c' s p hr hren hrk
    obtain ⟨a', b', hc', k1, k2⟩ := renames_and_inv H hren
    obtain ⟨sa, pa, sb, pb, ra, rb, hs, hp⟩ := ranks_and_inv H hrk
    rw [hc', hs, hp]
    exact ranks_and H (ha r a' sa pa hr k1 ra) (hb r b' sb pb hr k2 rb)
  · intro a b ha hb r c' s p hr hren hrk
    obtain ⟨a', b', hc', k1, k2⟩ := renames_or_inv H hren
    obtain ⟨sa, pa, sb, pb, ra, rb, hs, hp⟩ := ranks_or_inv H hrk
    rw [hc', hs, hp]
    exact ranks_or H (ha r a' sa pa hr k1 ra) (hb r b' sb pb hr k2 rb)
  · intro a ha r c' s p hr hren hrk
    obtain ⟨a', hc', k1⟩ := renames_all_inv H hren
    obtain ⟨sa, pa, ra, hs, hp⟩ := ranks_all_inv H hrk
    rw [hc', hs, hp]
    exact ranks_all H (ha (upV H r) a' sa pa (upV_isVarMap H hr) k1 ra)
  · intro a ha r c' s p hr hren hrk
    obtain ⟨a', hc', k1⟩ := renames_ex_inv H hren
    obtain ⟨sa, pa, ra, hs, hp⟩ := ranks_ex_inv H hrk
    rw [hc', hs, hp]
    exact ranks_ex H (ha (upV H r) a' sa pa (upV_isVarMap H hr) k1 ra)

/-- **The bound is invariant under internal renaming**, in the direction the
Leibniz rule consumes: if a renaming of a code is bounded, so is the code.  It
is here that codehood of the source is needed, since single-valuedness is
applied at the renamed code. -/
theorem quantBounded_of_renames (H : ZFAxioms mem) {b r a c' : V}
    (hc : IsFormCodeSem H a) (hr : IsVarMap H r) (hren : Renames H r a c')
    (h : QuantBounded H b c') : QuantBounded H b a := by
  obtain ⟨sa, pa, hra⟩ := rankTotal_of_isFormCodeSem H a hc
  obtain ⟨s, p, hr', hle⟩ := h
  have hren' : Ranks H c' sa pa :=
    rankRen_of_isFormCodeSem H a hc r c' sa pa hr hren hra
  obtain ⟨e1, e2⟩ :=
    rankUnique_of_isFormCodeSem H c' (renames_isFormCodeSem H hc hr hren)
      s p sa pa hr' hren'
  refine ⟨sa, pa, hra, ?_⟩
  rw [← e1, ← e2]
  exact hle

/-! ## The all-occurrences bound on a coded derivation -/

/-- Every member of the coded context is bounded. -/
def CtxBounded (H : ZFAxioms mem) (b g : V) : Prop :=
  ∀ x, MemCtx H x g → QuantBounded H b x

/-- "every member of the context in slot `g_i` is bounded by slot `b_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the member `x`        |
| `m+1`          | the caller's slot `m` |
-/
def fCtxBoundedF (b_i g_i : Nat) : Form :=
  fAll (fImp (fMemCtxF 0 (g_i+1)) (fQuantBoundedF (b_i+1) 0))

theorem fCtxBoundedF_spec (H : ZFAxioms mem) (ee : Nat → V) (b_i g_i : Nat) :
    Sat mem ee (fCtxBoundedF b_i g_i) ↔ CtxBounded H (ee b_i) (ee g_i) := by
  unfold CtxBounded
  constructor
  · intro h x hx
    exact (fQuantBoundedF_spec H _ (b_i+1) 0).mp
      (h x ((fMemCtxF_spec H _ 0 (g_i+1)).mpr hx))
  · intro h x hx
    exact (fQuantBoundedF_spec H _ (b_i+1) 0).mpr
      (h x ((fMemCtxF_spec H _ 0 (g_i+1)).mp hx))

/-- **Every judgement recorded by the certificate `d` is bounded by `b`**: its
conclusion and every member of its context.  By
`derStepBounded_of_derAllBounded` this is the every-occurrence bound and not
merely a node bound. -/
def DerAllBounded (H : ZFAxioms mem) (b d : V) : Prop :=
  ∀ n g c, mem (satTriple H n g c) d →
    (QuantBounded H b c ∧ CtxBounded H b g)

/-- `DerAllBounded` as a `Form`.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the conclusion `c`    |
| `1`            | the context `g`       |
| `2`            | the rank `n`          |
| `m+3`          | the caller's slot `m` |
-/
def fDerAllBoundedF (b_i d_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (d_i+3))
    (fAnd (fQuantBoundedF (b_i+3) 0) (fCtxBoundedF (b_i+3) 1)))))

theorem fDerAllBoundedF_spec (H : ZFAxioms mem) (ee : Nat → V) (b_i d_i : Nat) :
    Sat mem ee (fDerAllBoundedF b_i d_i) ↔
      DerAllBounded H (ee b_i) (ee d_i) := by
  unfold DerAllBounded
  constructor
  · intro h n g c hmem
    obtain ⟨h1, h2⟩ := h n g c ((fTripleMemF_spec H _ 2 1 0 (d_i+3)).mpr hmem)
    exact ⟨(fQuantBoundedF_spec H _ (b_i+3) 0).mp h1,
      (fCtxBoundedF_spec H _ (b_i+3) 1).mp h2⟩
  · intro h n g c hsat
    obtain ⟨h1, h2⟩ := h n g c ((fTripleMemF_spec H _ 2 1 0 (d_i+3)).mp hsat)
    exact ⟨(fQuantBoundedF_spec H _ (b_i+3) 0).mpr h1,
      (fCtxBoundedF_spec H _ (b_i+3) 1).mpr h2⟩

/-! ### The parameter-inclusive step, and its equivalence with the node bound

The seventeen clauses again, each with the bound imposed on every formula it
introduces as a rule parameter — the internal counterpart of the `annotations`
component of `Basic.nodeRank`.  These are not rendered as `Form`s and are not
part of the definition of `Con_n`; they exist so that
`derStepBounded_of_derAllBounded` can state what the node bound already
delivers. -/

/-- Implication introduction, with both components bounded. -/
def DImpIB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a e, IsFormCodeSem H a ∧ QuantBounded H b a ∧ QuantBounded H b e ∧
    c = kpair H (natV H 3) (kpair H a e) ∧ DerCite H D n (ctxCons H a g) e

/-- Implication elimination, with the antecedent bounded. -/
def DImpEB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a, IsFormCodeSem H a ∧ QuantBounded H b a ∧
    DerCite H D n g (kpair H (natV H 3) (kpair H a c)) ∧ DerCite H D n g a

/-- Excluded middle, with the disjunct bounded. -/
def DLemB (H : ZFAxioms mem) (b c : V) : Prop :=
  ∃ a, IsFormCodeSem H a ∧ QuantBounded H b a ∧
    c = kpair H (natV H 5) (kpair H a
      (kpair H (natV H 3) (kpair H a (kpair H (natV H 2) (vempty H)))))

/-- Conjunction introduction, with both conjuncts bounded. -/
def DAndIB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a e, QuantBounded H b a ∧ QuantBounded H b e ∧
    c = kpair H (natV H 4) (kpair H a e) ∧
    DerCite H D n g a ∧ DerCite H D n g e

/-- First conjunction elimination, with the discarded conjunct bounded. -/
def DAndE1B (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ e, IsFormCodeSem H e ∧ QuantBounded H b e ∧
    DerCite H D n g (kpair H (natV H 4) (kpair H c e))

/-- Second conjunction elimination, with the discarded conjunct bounded. -/
def DAndE2B (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a, IsFormCodeSem H a ∧ QuantBounded H b a ∧
    DerCite H D n g (kpair H (natV H 4) (kpair H a c))

/-- First disjunction introduction, with both disjuncts bounded. -/
def DOrI1B (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a e, IsFormCodeSem H a ∧ IsFormCodeSem H e ∧
    QuantBounded H b a ∧ QuantBounded H b e ∧
    c = kpair H (natV H 5) (kpair H a e) ∧ DerCite H D n g a

/-- Second disjunction introduction, with both disjuncts bounded. -/
def DOrI2B (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a e, IsFormCodeSem H a ∧ IsFormCodeSem H e ∧
    QuantBounded H b a ∧ QuantBounded H b e ∧
    c = kpair H (natV H 5) (kpair H a e) ∧ DerCite H D n g e

/-- Disjunction elimination, with both disjuncts bounded. -/
def DOrEB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a e, IsFormCodeSem H a ∧ IsFormCodeSem H e ∧
    QuantBounded H b a ∧ QuantBounded H b e ∧
    DerCite H D n g (kpair H (natV H 5) (kpair H a e)) ∧
    DerCite H D n (ctxCons H a g) c ∧ DerCite H D n (ctxCons H e g) c

/-- Universal introduction, with the body bounded. -/
def DAllIB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a g', IsFormCodeSem H a ∧ QuantBounded H b a ∧
    c = kpair H (natV H 6) a ∧ ShiftsCtx H g g' ∧ DerCite H D n g' a

/-- Universal elimination, with the body bounded. -/
def DAllEB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a k, IsFormCodeSem H a ∧ QuantBounded H b a ∧ mem k (omegaV H) ∧
    Renames H (instMap H k) a c ∧
    DerCite H D n g (kpair H (natV H 6) a)

/-- Existential introduction, with the body and the instance bounded. -/
def DExIB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a k a', IsFormCodeSem H a ∧ QuantBounded H b a ∧ QuantBounded H b a' ∧
    mem k (omegaV H) ∧ c = kpair H (natV H 7) a ∧
    Renames H (instMap H k) a a' ∧ DerCite H D n g a'

/-- Existential elimination, with the body and the shifted conclusion
bounded. -/
def DExEB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ a g' c', IsFormCodeSem H a ∧ QuantBounded H b a ∧ QuantBounded H b c' ∧
    ShiftsCtx H g g' ∧ Renames H (succMap H) c c' ∧
    DerCite H D n g (kpair H (natV H 7) a) ∧
    DerCite H D n (ctxCons H a g') c'

/-- The Leibniz rule, with the substituted formula and the cited instance
bounded. -/
def DEqElimB (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  ∃ i j a ci, mem i (omegaV H) ∧ mem j (omegaV H) ∧ IsFormCodeSem H a ∧
    QuantBounded H b a ∧ QuantBounded H b ci ∧
    Renames H (instMap H i) a ci ∧ Renames H (instMap H j) a c ∧
    DerCite H D n g (kpair H (natV H 1) (kpair H i j)) ∧
    DerCite H D n g ci

/-- The seventeen clauses with every formula-valued rule parameter bounded.
The three parameter-free rules — assumption, ex falso and reflexivity — are
taken over unchanged. -/
def DerStepBounded (H : ZFAxioms mem) (b D n g c : V) : Prop :=
  DAss H g c ∨ DImpIB H b D n g c ∨ DImpEB H b D n g c ∨ DBotE H D n g ∨
  DLemB H b c ∨ DAndIB H b D n g c ∨ DAndE1B H b D n g c ∨
  DAndE2B H b D n g c ∨ DOrI1B H b D n g c ∨ DOrI2B H b D n g c ∨
  DOrEB H b D n g c ∨ DAllIB H b D n g c ∨ DAllEB H b D n g c ∨
  DExIB H b D n g c ∨ DExEB H b D n g c ∨ DEqRefl H c ∨
  DEqElimB H b D n g c

/-- A bounded step is a step: the bounds are extra conjuncts and nothing
else. -/
theorem derStep_of_derStepBounded (H : ZFAxioms mem) {b D n g c : V}
    (h : DerStepBounded H b D n g c) : DerStep H D n g c := by
  rcases h with h | ⟨a, e, h1, _, _, h2, h3⟩ | ⟨a, h1, _, h2, h3⟩ | h |
    ⟨a, h1, _, h2⟩ | ⟨a, e, _, _, h1, h2, h3⟩ | ⟨e, h1, _, h2⟩ |
    ⟨a, h1, _, h2⟩ | ⟨a, e, h1, h2, _, _, h3, h4⟩ |
    ⟨a, e, h1, h2, _, _, h3, h4⟩ | ⟨a, e, h1, h2, _, _, h3, h4, h5⟩ |
    ⟨a, g', h1, _, h2, h3, h4⟩ | ⟨a, k, h1, _, h2, h3, h4⟩ |
    ⟨a, k, a', h1, _, _, h2, h3, h4, h5⟩ |
    ⟨a, g', c', h1, _, _, h2, h3, h4, h5⟩ | h |
    ⟨i, j, a, ci, h1, h2, h3, _, _, h4, h5, h6, h7⟩
  · exact derStep_ass H h
  · exact derStep_impI H ⟨a, e, h1, h2, h3⟩
  · exact derStep_impE H ⟨a, h1, h2, h3⟩
  · exact derStep_botE H h
  · exact derStep_lem H ⟨a, h1, h2⟩
  · exact derStep_andI H ⟨a, e, h1, h2, h3⟩
  · exact derStep_andE1 H ⟨e, h1, h2⟩
  · exact derStep_andE2 H ⟨a, h1, h2⟩
  · exact derStep_orI1 H ⟨a, e, h1, h2, h3, h4⟩
  · exact derStep_orI2 H ⟨a, e, h1, h2, h3, h4⟩
  · exact derStep_orE H ⟨a, e, h1, h2, h3, h4, h5⟩
  · exact derStep_allI H ⟨a, g', h1, h2, h3, h4⟩
  · exact derStep_allE H ⟨a, k, h1, h2, h3, h4⟩
  · exact derStep_exI H ⟨a, k, a', h1, h2, h3, h4, h5⟩
  · exact derStep_exE H ⟨a, g', c', h1, h2, h3, h4, h5⟩
  · exact derStep_eqRefl H h
  · exact derStep_eqElim H ⟨i, j, a, ci, h1, h2, h3, h4, h5, h6, h7⟩

/-- The bound at a cited premise: a citation names a triple of the
certificate, so the node bound applies to it. -/
theorem quantBounded_of_derCite (H : ZFAxioms mem) {b d n g c : V}
    (hb : DerAllBounded H b d) (h : DerCite H d n g c) :
    QuantBounded H b c ∧ CtxBounded H b g := by
  obtain ⟨m, -, hmem⟩ := h
  exact hb m g c hmem

/-- **The node bound is the every-occurrence bound.**  At every judgement of a
bounded certificate the rule that justifies it can be read with all of its
formula parameters bounded.  Sixteen of the seventeen cases are the subcode
lemmas applied to the conclusion of the node or of a cited premise, or a
context member of a cited premise; the Leibniz rule is the one that needs
invariance of the bound under internal renaming. -/
theorem derStepBounded_of_derAllBounded (H : ZFAxioms mem) {b d n g c : V}
    (hbo : mem b (omegaV H)) (hb : DerAllBounded H b d)
    (hmem : mem (satTriple H n g c) d) (h : DerStep H d n g c) :
    DerStepBounded H b d n g c := by
  have hc : QuantBounded H b c := (hb n g c hmem).1
  rcases h with h | ⟨a, e, h1, h2, h3⟩ | ⟨a, h1, h2, h3⟩ | h |
    ⟨a, h1, h2⟩ | ⟨a, e, h1, h2, h3⟩ | ⟨e, h1, h2⟩ | ⟨a, h1, h2⟩ |
    ⟨a, e, h1, h2, h3, h4⟩ | ⟨a, e, h1, h2, h3, h4⟩ |
    ⟨a, e, h1, h2, h3, h4, h5⟩ | ⟨a, g', h1, h2, h3, h4⟩ |
    ⟨a, k, h1, h2, h3, h4⟩ | ⟨a, k, a', h1, h2, h3, h4, h5⟩ |
    ⟨a, g', c', h1, h2, h3, h4, h5⟩ | h |
    ⟨i, j, a, ci, h1, h2, h3, h4, h5, h6, h7⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨a, e, h1, ?_, ?_, h2, h3⟩)
    · exact (quantBounded_imp H hbo (h2 ▸ hc)).1
    · exact (quantBounded_imp H hbo (h2 ▸ hc)).2
  · refine Or.inr (Or.inr (Or.inl ⟨a, h1, ?_, h2, h3⟩))
    exact (quantBounded_imp H hbo (quantBounded_of_derCite H hb h2).1).1
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, h1, ?_, h2⟩))))
    exact (quantBounded_or H hbo (h2 ▸ hc)).1
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, e, ?_, ?_, h1, h2, h3⟩)))))
    · exact (quantBounded_and H hbo (h1 ▸ hc)).1
    · exact (quantBounded_and H hbo (h1 ▸ hc)).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e, h1, ?_, h2⟩))))))
    exact (quantBounded_and H hbo (quantBounded_of_derCite H hb h2).1).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, h1, ?_, h2⟩)))))))
    exact (quantBounded_and H hbo (quantBounded_of_derCite H hb h2).1).1
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨a, e, h1, h2, ?_, ?_, h3, h4⟩))))))))
    · exact (quantBounded_or H hbo (h3 ▸ hc)).1
    · exact (quantBounded_or H hbo (h3 ▸ hc)).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨a, e, h1, h2, ?_, ?_, h3, h4⟩)))))))))
    · exact (quantBounded_or H hbo (h3 ▸ hc)).1
    · exact (quantBounded_or H hbo (h3 ▸ hc)).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨a, e, h1, h2, ?_, ?_, h3, h4, h5⟩))))))))))
    · exact (quantBounded_or H hbo (quantBounded_of_derCite H hb h3).1).1
    · exact (quantBounded_or H hbo (quantBounded_of_derCite H hb h3).1).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, g', h1, ?_, h2, h3, h4⟩)))))))))))
    exact quantBounded_all H hbo (h2 ▸ hc)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨a, k, h1, ?_, h2, h3, h4⟩))))))))))))
    exact quantBounded_all H hbo (quantBounded_of_derCite H hb h4).1
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨a, k, a', h1, ?_, ?_, h2, h3, h4, h5⟩)))))))))))))
    · exact quantBounded_ex H hbo (h3 ▸ hc)
    · exact (quantBounded_of_derCite H hb h5).1
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨a, g', c', h1, ?_, ?_, h2, h3, h4, h5⟩))))))))))))))
    · exact quantBounded_ex H hbo (quantBounded_of_derCite H hb h4).1
    · exact (quantBounded_of_derCite H hb h5).1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨i, j, a, ci, h1, h2, h3, ?_, ?_, h4, h5, h6, h7⟩)))))))))))))))
    · exact quantBounded_of_renames H h3 (instMap_isVarMap H h2) h5 hc
    · exact (quantBounded_of_derCite H hb h7).1

/-! ## The sentence `Con_n(ZFC)`

For each metatheoretic `n` the sentence says: no set is at once a coded
derivation of the falsity code from the empty context and bounded, at every
occurrence, by the numeral of `n`.  The bound is written as the numeral rather
than quantified, which is what keeps the parameter metatheoretic. -/

/-- The body of the sentence, with four leading binders.

| de Bruijn slot | contents                      |
| -------------- | ----------------------------- |
| `0`            | the candidate derivation `d`  |
| `1`            | the falsity code              |
| `2`            | the empty context code        |
| `3`            | the numeral bound             |
-/
def logicConBodyF (n : Nat) : Form :=
  fAll (fAll (fAll (fAll
    (fImp (fNumF 3 n)
      (fImp (fCtxNilF 2)
        (fImp (fTaggedEmptyF 1 2)
          (fImp (fAnd (fDerivesF 0 2 1) (fDerAllBoundedF 3 0)) fBot)))))))

theorem conBodyF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V) :
    Sat mem ee (logicConBodyF n) ↔
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := by
  constructor
  · rintro h ⟨d, hder, hbnd⟩
    exact h (natV H n) (ctxNil H) (kpair H (natV H 2) (vempty H)) d
      ((fNumF_spec H n 3 _).mpr rfl)
      ((fCtxNilF_spec H _ 2).mpr rfl)
      ((fTaggedEmptyF_spec H _ 1 2).mpr rfl)
      ⟨(fDerivesF_spec H _ 0 2 1).mpr hder,
        (fDerAllBoundedF_spec H _ 3 0).mpr hbnd⟩
  · intro h b g c d hb hg hc hd
    have hb' : b = natV H n := (fNumF_spec H n 3 _).mp hb
    have hg' : g = ctxNil H := (fCtxNilF_spec H _ 2).mp hg
    have hc' : c = kpair H (natV H 2) (vempty H) :=
      (fTaggedEmptyF_spec H _ 1 2).mp hc
    have hder := (fDerivesF_spec H _ 0 2 1).mp hd.1
    have hbnd := (fDerAllBoundedF_spec H _ 3 0).mp hd.2
    rw [hg', hc'] at hder
    rw [hb'] at hbnd
    exact h ⟨d, hder, hbnd⟩

/-- **`Con_n(ZFC)`**, as an object-language sentence: the universal closure of
`logicConBodyF n`.  Sealing is what makes sentencehood free; the body is closed in
any case, but computing that over a formula of this size is not worth the
elaboration. -/
def logicConForm (n : Nat) : Form := sealF (logicConBodyF n)

theorem sentence_conForm (n : Nat) : Sentence (logicConForm n) :=
  Sentence_seal _

/-- **The arbitrary-model characterization.**  In any model of the `ZFAxioms`
bundle, `Con_n(ZFC)` holds exactly when no coded derivation of falsity from the
empty context has all of its occurrences bounded by the numeral of `n`. -/
theorem sat_logicConForm_iff (H : ZFAxioms mem) (n : Nat) :
    (∀ e : Nat → V, Sat mem e (logicConForm n)) ↔
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := by
  have hs := seal_valid (mem := mem) (logicConBodyF n)
  constructor
  · intro h
    exact (conBodyF_spec H n (fun _ => vempty H)).mp (hs.mp h _)
  · intro h
    exact hs.mpr (fun e => (conBodyF_spec H n e).mpr h)

end CodedRank

/-! ## From models of ZFC to the object-level derivation

The endpoint bridge.  `godel_completeness_for_theories` turns truth in every
model of a sentence theory into a derivation from that theory, and `ZFCax_s` is
a sentence theory by `Sentences_ZFC`, so the remaining obligation is exactly
"the sentence holds in every model" — which is what the reflection layer will
supply, and which nothing here asserts. -/

section Endpoint

open SetTheory.FirstOrderClassicalCompleteness

/-- A model of the sealed ZFC axioms carries the semantic axiom bundle every
internal result of this project is relative to.

This is assembled from the extraction bridges of `ZF.Zf` and belongs beside
them; it is proved here because no consumer of `ZF.Zf` had needed it before. -/
theorem zfAxioms_of_zfcModel {Dom : Type} {m : Dom → Dom → Prop} (v : Nat → Dom)
    (hmodel : ∀ g, ZFCax_s g → Sat m v g) : ZFAxioms m := by
  have hx : ∀ f, ZFax_s f → Sat m v f := fun f hf => hmodel f (Or.inl hf)
  exact
    { ext := bridge_Ext_fwd
        (extract ZFax_s v Ext_form hx (Or.inl rfl))
      sep := bridge_Sep_fwd (fun phi =>
        extract ZFax_s v (Sep_form phi) hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨phi, rfl⟩))))))))
      pair := bridge_Pair_fwd
        (extract ZFax_s v Pair_form hx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      union := bridge_Union_fwd
        (extract ZFax_s v Union_form hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      inf := bridge_Inf_fwd v
        (extract ZFax_s v Inf_form hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) v)
      repl := bridge_Repl_fwd (fun psi =>
        extract ZFax_s v (Repl_form psi) hx
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨psi, rfl⟩))))))))  }

/-- If no model of ZFC carries a bounded coded derivation of falsity, then
`Con_n(ZFC)` is a semantic consequence of ZFC. -/
theorem logicConForm_semanticConsequence (n : Nat)
    (h : ∀ (Dom : Type) (m : Dom → Dom → Prop) (H : ZFAxioms m),
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d) :
    TheorySemanticConsequence ZFCax_s (logicConForm n) := by
  intro Dom m v hmodel
  exact (sat_logicConForm_iff (zfAxioms_of_zfcModel v hmodel) n).mpr
    (h Dom m (zfAxioms_of_zfcModel v hmodel)) v

/-- **The endpoint bridge.**  Truth of `Con_n(ZFC)` in every model of ZFC
yields an object-level derivation of it from ZFC.  This is
`godel_completeness_for_theories` at the sentence theory `ZFCax_s`; it is the
last step of the intended argument, and the only thing still missing in front
of it is the hypothesis. -/
theorem zfcprov_logicConForm_of_valid (n : Nat)
    (h : TheorySemanticConsequence ZFCax_s (logicConForm n)) :
    TheorySyntacticConsequence ZFCax_s (logicConForm n) :=
  godel_completeness_for_theories ZFCax_s (logicConForm n) Sentences_ZFC h

/-- The two steps composed: the whole remaining obligation of the project, in
one statement. -/
theorem zfcprov_logicConForm_of_no_bounded_refutation (n : Nat)
    (h : ∀ (Dom : Type) (m : Dom → Dom → Prop) (H : ZFAxioms m),
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d) :
    TheorySyntacticConsequence ZFCax_s (logicConForm n) :=
  zfcprov_logicConForm_of_valid n (logicConForm_semanticConsequence n h)

end Endpoint

end BoundedZFCConsistency
end LeanProofs
