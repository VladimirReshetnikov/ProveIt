import BusyBeaver.ZFC.TransRec

/- Explicit old hierarchy interfaces and definitional shapes, plus the generic
   no-monotonicity interface. Source-only client; compiler results are separate. -/
namespace SetTheory.BusyBeaver.ZFC.TransRec15Api
open NamedZF NForm InternalOrd InternalRank
universe u
variable {V : Type u} {mem : V → V → Prop}

private def legacyApprox (H : ZFAxioms mem) (R : V → V → Prop) (f d : V) : Prop :=
  (∀ p, mem p f → ∃ b S, mem b d ∧ p = kpair H b S) ∧
  (∀ b, mem b d → ∃ S, mem (kpair H b S) f) ∧
  (∀ b S S', mem (kpair H b S) f → mem (kpair H b S') f → S = S') ∧
  (∀ b S, mem (kpair H b S) f →
    ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ R z T)

private def legacyApproxF (rF : Nat → Nat → NForm) (f d : Nat) : NForm :=
  let n := f + d + 1
  let c1 := NForm.all n (.imp (.mem n f) (.ex (n + 1) (.ex (n + 2)
    (.and (.mem (n + 1) d) (kpairF n (n + 1) (n + 2))))))
  let c2 := NForm.all n (.imp (.mem n d) (.ex (n + 1) (pmemF f n (n + 1))))
  let c3 := NForm.all n (.all (n + 1) (.all (n + 2)
    (.imp (.and (pmemF f n (n + 1)) (pmemF f n (n + 2))) (.eq (n + 1) (n + 2)))))
  let rhs := NForm.ex (n + 3) (.ex (n + 4) (.and (.mem (n + 3) n)
    (.and (pmemF f (n + 3) (n + 4)) (rF (n + 2) (n + 4)))))
  let c4 := NForm.all n (.all (n + 1) (.imp (pmemF f n (n + 1))
    (.all (n + 2) ((NForm.mem (n + 2) (n + 1)).iff rhs))))
  .and c1 (.and c2 (.and c3 c4))

private def legacyStageF (rF : Nat → Nat → NForm) (a S : Nat) : NForm :=
  let n := a + S + 1
  .ex n (.and (.ex (n + 1) (.and (succF (n + 1) a)
    (legacyApproxF rF n (n + 1)))) (pmemF n a S))

theorem cumulative_shape (H : ZFAxioms mem) (a S : V) :
    IsV H a S ↔ ∃ f, legacyApprox H (Sub mem) f (vsucc H a) ∧ mem (kpair H a S) f := Iff.rfl

theorem operation_shape (H : ZFAxioms mem) (G : V → V) (a S : V) :
    TransRec.IsStage H G a S ↔
      ∃ f, legacyApprox H (fun z T => mem z (G T)) f (vsucc H a) ∧ mem (kpair H a S) f := Iff.rfl

theorem approximation_shape (H : ZFAxioms mem) (G : V → V) (f d : V) :
    TransRec.Approx H G f d ↔ legacyApprox H (fun z T => mem z (G T)) f d := Iff.rfl

theorem cumulative_formula (a S : Nat) : isVF a S = legacyStageF subF a S := rfl

theorem operation_formula {G : V → V} (D : TransRec.DefOp mem G) (a S : Nat) :
    TransRec.isStageF D a S = legacyStageF (TransRec.inGF D) a S := rfl

theorem cumulative_semantics (H : ZFAxioms mem) (ρ : Nat → V) (a S : Nat) :
    NSat mem ρ (isVF a S) ↔ IsV H (ρ a) (ρ S) := nsat_isVF H ρ a S

theorem cumulative_exists (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) {a : V} (ha : Ord mem a) :
    ∃ S, IsV H a S := isV_exists H hR hP ha

theorem cumulative_unique (H : ZFAxioms mem) (hR : Regular mem) {a S S' : V}
    (ha : Ord mem a) (h : IsV H a S) (h' : IsV H a S') : S = S' := isV_unique H hR ha h h'

theorem cumulative_spec (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) {a S : V} (ha : Ord mem a) (h : IsV H a S) :
    ∀ z, mem z S ↔ ∃ c T, mem c a ∧ IsV H c T ∧ Sub mem z T := isV_spec H hR hP ha h

theorem cumulative_mono (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) {a c S T : V}
    (ha : Ord mem a) (hc : mem c a) (hT : IsV H c T) (hS : IsV H a S) :
    Sub mem T S := isV_mono H hR hP ha hc hT hS

theorem cumulative_trans (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) {a S : V}
    (ha : Ord mem a) (hS : IsV H a S) : Trans mem S := isV_trans H hR hP ha hS

theorem operation_semantics (H : ZFAxioms mem) {G : V → V}
    (D : TransRec.DefOp mem G) (ρ : Nat → V) (a S : Nat) :
    NSat mem ρ (TransRec.isStageF D a S) ↔ TransRec.IsStage H G (ρ a) (ρ S) :=
  TransRec.nsat_isStageF H D ρ a S

theorem operation_exists (H : ZFAxioms mem) (hR : Regular mem) {G : V → V}
    (D : TransRec.DefOp mem G) {a : V} (ha : Ord mem a) :
    ∃ S, TransRec.IsStage H G a S := TransRec.stage_exists' H hR D ha

theorem operation_unique (H : ZFAxioms mem) (hR : Regular mem) {G : V → V} {a S S' : V}
    (ha : Ord mem a) (h : TransRec.IsStage H G a S) (h' : TransRec.IsStage H G a S') :
    S = S' := TransRec.stage_unique H hR ha h h'

theorem operation_spec (H : ZFAxioms mem) (hR : Regular mem) {G : V → V}
    (D : TransRec.DefOp mem G) {a S : V} (ha : Ord mem a) (h : TransRec.IsStage H G a S) :
    ∀ z, mem z S ↔ ∃ c T, mem c a ∧ TransRec.IsStage H G c T ∧ mem z (G T) :=
  TransRec.stage_spec H hR D ha h

theorem operation_mono (H : ZFAxioms mem) (hR : Regular mem) {G : V → V}
    (D : TransRec.DefOp mem G) {a c S T : V} (ha : Ord mem a) (hc : mem c a)
    (hT : TransRec.IsStage H G c T) (hS : TransRec.IsStage H G a S) :
    Sub mem T S := TransRec.stage_mono H hR D ha hc hT hS

/-- Uniqueness needs no definability or set-of-values premise. -/
theorem relation_unique (H : ZFAxioms mem) (hR : Regular mem) {R : V → V → Prop}
    {a S S' : V} (ha : Ord mem a) (h : RStage H R a S) (h' : RStage H R a S') :
    S = S' := rstage_unique H hR ha h h'

/-- No monotonicity hypothesis on R is present. -/
theorem relation_mono (H : ZFAxioms mem) (hR : Regular mem) {R : V → V → Prop}
    {rF : Nat → Nat → NForm} (hrF : RDef mem R rF) (hS : RSets mem R)
    {a c S T : V} (ha : Ord mem a) (hc : mem c a) (hT : RStage H R c T) (hSa : RStage H R a S) :
    Sub mem T S := rstage_mono H hR hrF hS ha hc hT hSa

#print axioms cumulative_shape
#print axioms operation_shape
#print axioms approximation_shape
#print axioms cumulative_formula
#print axioms operation_formula
#print axioms cumulative_semantics
#print axioms cumulative_exists
#print axioms cumulative_unique
#print axioms cumulative_spec
#print axioms cumulative_mono
#print axioms cumulative_trans
#print axioms operation_semantics
#print axioms operation_exists
#print axioms operation_unique
#print axioms operation_spec
#print axioms operation_mono
#print axioms relation_unique
#print axioms relation_mono
end SetTheory.BusyBeaver.ZFC.TransRec15Api
