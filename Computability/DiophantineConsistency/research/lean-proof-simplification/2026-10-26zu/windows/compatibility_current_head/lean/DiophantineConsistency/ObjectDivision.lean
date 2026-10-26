import DiophantineConsistency.ObjectListHead
import DiophantineConsistency.OrderedWindow

/-! # Euclidean division throughout the internal omega

Existence uses a displayed object formula and internal omega induction.
There is no appeal to an external well-foundedness principle on the carrier.
-/
noncomputable section
namespace DiophantineConsistency.ObjectDivision
set_option maxRecDepth 16000
open SetTheory SetTheory.Form ObjectOmegaSemiring
open LeanProofs.BoundedZFCConsistency
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

def DivisionRel (q r n d : N H) : Prop := n=q*d+r ∧ r<d

private def equation : Expr (Fin 4) :=
  Expr.sub (.var 2) (.add (.mul (.var 0) (.var 3)) (.var 1))

private theorem equation_zero_iff (x : Fin 4 → N H) :
    equation.SemiringZero x ↔ x 2=x 0*x 3+x 1 := by
  simp [equation,Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring]

attribute [local irreducible] equation

private def stageForm : Form :=
  fEx (fEx (fAnd (fNatF 1) (fAnd (fNatF 0) (fAnd (fMem 0 3)
    (ObjectPolynomial.equationForm equation ![1,0,2,3])))))

private theorem stageForm_spec (n d : N H) (ee : ℕ → V) :
    Sat mem (scons n.val (scons d.val ee)) stageForm ↔
      ∃ q r : N H,DivisionRel H q r n d := by
  constructor
  · rintro ⟨q,r,hq,hr,hlt,he⟩
    let qq : N H := ⟨q,(fNatF_spec H _ 1).mp hq⟩
    let rr : N H := ⟨r,(fNatF_spec H _ 0).mp hr⟩
    refine ⟨qq,rr,?_,hlt⟩
    have he' := (ObjectPolynomial.equationForm_spec H equation ![1,0,2,3] _).mp he
    have hv : (scons r (scons q (scons n.val (scons d.val ee)))) ∘
        (![1,0,2,3] : Fin 4 → ℕ) =
        (fun i => ((![qq,rr,n,d] : Fin 4 → N H) i).val) := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at he'
    exact (equation_zero_iff H _).mp ((ObjectNaturalSemiring.equationRel_iff H equation _).mp he')
  · rintro ⟨q,r,he,hlt⟩
    refine ⟨q.val,r.val,(fNatF_spec H _ 1).mpr q.property,
      (fNatF_spec H _ 0).mpr r.property,hlt,?_⟩
    apply (ObjectPolynomial.equationForm_spec H equation ![1,0,2,3] _).mpr
    have hh := (ObjectNaturalSemiring.equationRel_iff H equation (![q,r,n,d] : Fin 4 → N H)).mpr
      ((equation_zero_iff H _).mpr he)
    convert hh using 1
    funext i
    fin_cases i <;> rfl

private theorem successor_step (n d : N H) (h : ∃ q r,DivisionRel H q r n d) :
    ∃ q r,DivisionRel H q r (n+1) d := by
  obtain ⟨q,r,he,hr⟩ := h
  obtain ⟨s,hs⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H r d).mp hr
  have hr1 : r+1≤d := (ObjectNaturalOrder.Natural.le_iff_exists_add H _ _).mpr
    ⟨s,by rw [hs]; ac_rfl⟩
  rcases lt_or_eq_of_le hr1 with hlt | heq
  · exact ⟨q,r+1,by rw [he]; ring,hlt⟩
  · refine ⟨q+1,0,?_,?_⟩
    · rw [he,← heq]
      ring
    · exact (ObjectNaturalDiscrete.lt_iff_exists_add_one H 0 d).mpr ⟨r,by simpa using heq.symm⟩

theorem division_exists (n d : N H) (hd : 0<d) : ∃ q r,DivisionRel H q r n d := by
  let ee : ℕ → V := fun _ => vempty H
  have hind : ∀ k,mem k (omegaV H) → Sat mem (scons k (scons d.val ee)) stageForm := by
    apply omega_ind H stageForm (scons d.val ee)
    · apply (stageForm_spec H 0 d ee).mpr
      exact ⟨0,0,by simp,hd⟩
    · intro k hk ih
      apply (stageForm_spec H ⟨vsucc H k,omega_succ H k hk⟩ d ee).mpr
      have hs : (⟨vsucc H k,omega_succ H k hk⟩ : N H)=(⟨k,hk⟩ : N H)+1 := by
        apply Subtype.ext
        change vsucc H k=ObjectMultiplication.addValue H k (natV H 1)
        change vsucc H k=ObjectMultiplication.addValue H k (vsucc H (vempty H))
        rw [ObjectMultiplicationLaws.addValue_succ_right H hk (vempty_in_omega H),
          ObjectMultiplicationLaws.addValue_zero_right H hk]
      rw [hs]
      exact successor_step H ⟨k,hk⟩ d ((stageForm_spec H ⟨k,hk⟩ d ee).mp ih)
  exact (stageForm_spec H n d ee).mp (hind n.val n.property)

theorem division_unique {q r q' r' n d : N H}
    (h : DivisionRel H q r n d) (h' : DivisionRel H q' r' n d) : q=q' ∧ r=r' := by
  have window {a b : N H} (he : n=a*d+b) (hb : b<d) :
      a*d≤n ∧ n<(a+1)*d := by
    rw [he]
    exact ⟨le_self_add, by
      simpa only [add_mul,one_mul,add_comm] using add_lt_add_left hb (a*d)⟩
  have step_le {a b : N H} (hab : a<b) : a+1≤b := by
    obtain ⟨s,hs⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H a b).mp hab
    exact (ObjectNaturalOrder.Natural.le_iff_exists_add H _ _).mpr ⟨s,by rw [hs]; ac_rfl⟩
  have hq := OrderedWindow.index_unique (fun a : N H => a+1) step_le (fun a => a*d)
    (fun _ _ h => mul_le_mul_of_nonneg_right h (zero_le : (0 : N H)≤d))
    (window h.1 h.2).1 (window h.1 h.2).2 (window h'.1 h'.2).1 (window h'.1 h'.2).2
  subst q'
  exact ⟨rfl,add_left_cancel (h.1.symm.trans h'.1)⟩

private theorem exists_divmod (n d : N H) (hd : d≠0) :
    ∃ p : N H × N H,DivisionRel H p.1 p.2 n d := by
  have hp : 0<d := lt_of_le_of_ne (ObjectNaturalOrder.Natural.zero_le H d) hd.symm
  obtain ⟨q,r,h⟩ := division_exists H n d hp
  exact ⟨(q,r),h⟩

/-- Semantic quotient/remainder, with the usual zero-denominator convention. -/
def divmod (n d : N H) : N H × N H :=
  if hd : d=0 then (0,n) else Classical.choose (exists_divmod H n d hd)

theorem divmod_zero (n : N H) : divmod H n 0=(0,n) := by simp [divmod]

theorem divmod_spec (n d : N H) (hd : d≠0) :
    DivisionRel H (divmod H n d).1 (divmod H n d).2 n d := by
  simpa only [divmod,dif_neg hd] using Classical.choose_spec (exists_divmod H n d hd)

theorem division_iff (q r n d : N H) :
    DivisionRel H q r n d ↔ 0<d ∧ divmod H n d=(q,r) := by
  constructor
  · intro h
    have hd : 0<d := (ObjectNaturalOrder.Natural.zero_le H r).trans_lt h.2
    have hu := division_unique H (divmod_spec H n d hd.ne') h
    exact ⟨hd,Prod.ext hu.1 hu.2⟩
  · rintro ⟨hd,he⟩
    simpa only [he] using divmod_spec H n d hd.ne'

/-- This is the exact positive-guarded, one-slack local certificate. -/
theorem exists_certificate_iff (q r n d : N H) :
    (∃ s,n=q*d+r ∧ d=r+s+1) ↔ 0<d ∧ divmod H n d=(q,r) := by
  rw [← division_iff]
  exact ⟨fun ⟨s,hn,hd⟩ => ⟨hn,(ObjectNaturalDiscrete.lt_iff_exists_add_one H r d).mpr ⟨s,hd⟩⟩,
    fun ⟨hn,hr⟩ => by
      obtain ⟨s,hs⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H r d).mp hr
      exact ⟨s,hn,hs⟩⟩

/-- At numerals this is the actual external quotient/remainder convention. -/
theorem divmod_cast (n d : ℕ) : divmod H (n : N H) (d : N H)=
    ((n/d : N H),(n%d : N H)) := by
  by_cases hd : d=0
  · subst d
    simp only [Nat.cast_zero,divmod_zero,Nat.div_zero,Nat.mod_zero]
  · apply ((division_iff H _ _ _ _).mp ?_).2
    refine ⟨?_,(ObjectNaturalDiscrete.cast_lt_cast H _ _).mpr (Nat.mod_lt n (Nat.pos_of_ne_zero hd))⟩
    exact_mod_cast (Nat.div_add_mod' n d).symm

def totalForm : Form := sealF
  (fImp (fAnd (fNatF 0) (fAnd (fNatF 1) (fImp (fEmptyF 1) fBot))) stageForm)
theorem sentence_totalForm : Sentence totalForm := Sentence_seal _

theorem zfc_proves_total : BProv ZFCax_s [] totalForm := by
  refine completeness_inf_context ZFCax_s [] totalForm Sentences_ZFC ?_
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  apply (seal_valid (mem := relation) _).mpr ?_ env
  intro ee h
  have hn := (fNatF_spec HH ee 0).mp h.1
  have hd := (fNatF_spec HH ee 1).mp h.2.1
  have hd0 : (⟨ee 1,hd⟩ : Natural HH)≠0 := by
    intro he
    exact h.2.2 ((fEmptyF_spec HH ee 1).mpr (congrArg Subtype.val he))
  have hp := division_exists HH ⟨ee 0,hn⟩ ⟨ee 1,hd⟩
    (lt_of_le_of_ne (ObjectNaturalOrder.Natural.zero_le HH _) hd0.symm)
  have hs := (stageForm_spec HH ⟨ee 0,hn⟩ ⟨ee 1,hd⟩ (fun n => ee (n+2))).mpr hp
  have he : scons (ee 0) (scons (ee 1) (fun n => ee (n+2)))=ee := by
    funext n
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl
  exact he ▸ hs

end DiophantineConsistency.ObjectDivision
