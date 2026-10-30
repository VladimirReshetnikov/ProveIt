import ZFCinPA.ModelCodedBindOne
import BusyBeaver.ZFC.ArithmeticCantor
noncomputable section

/-!
Represented decoder for the literal C254 base4 formula code.
A course-of-values sequence computes all entries through its internal index.
The source Cantor projections and the target syntax/HFS encodings are separate.
This module concerns syntax and formula well-formedness, not proof translation.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoder254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Native target relation on two named free variables; symbol 0 is equality,
    symbol 1 is membership in the actual fixed set language. -/
noncomputable def atomCode (symbol a b : V) : V := ^rel 2 symbol ?[^&a,^&b]
def atomCodeDef : 𝚺₁.Semisentence 4 := .mkSigma “out symbol a b.
  ∃ ta, !qqFvarDef ta a ∧ ∃ tb, !qqFvarDef tb b ∧
  ∃ args, !mkVec₂Def args ta tb ∧ !qqRelDef out 2 symbol args”
instance atomCode_defined : 𝚺₁-Function₃[V] atomCode via atomCodeDef :=
  .mk fun e => by simp [atomCodeDef,atomCode]

lemma atomCode_isFormula (symbol a b : V) (hr : (ℒₛₑₜ).IsRel 2 symbol) :
    IsFormula ℒₛₑₜ (atomCode symbol a b) := by simp [atomCode,hr]
lemma eqCode_isFormula (a b : V) : IsFormula ℒₛₑₜ (atomCode 0 a b) := by
  apply atomCode_isFormula
  simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 0)).mpr
    ⟨Language.Set.Rel.eq,rfl⟩
lemma memCode_isFormula (a b : V) : IsFormula ℒₛₑₜ (atomCode 1 a b) := by
  apply atomCode_isFormula
  simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
    ⟨Language.Set.Rel.mem,rfl⟩

/-- Match Code254.T0: membership(0,0) implies itself, rather than primitive Bot. -/
noncomputable def zeroFormula : V := imp ℒₛₑₜ (atomCode 1 0 0) (atomCode 1 0 0)
def zeroFormulaDef : 𝚺₁.Semisentence 1 := .mkSigma “out.
  ∃ f, !atomCodeDef f 1 0 0 ∧ !(impGraph ℒₛₑₜ) out f f”
instance zeroFormula_defined : 𝚺₁-Function₀[V] zeroFormula via zeroFormulaDef :=
  .mk fun e => by simp [zeroFormulaDef,zeroFormula]
lemma zeroFormula_isFormula : IsFormula ℒₛₑₜ (zeroFormula : V) := by
  simp [zeroFormula,memCode_isFormula]

/-- Total row on arbitrary histories. Range/validity of lookups is proved later. -/
noncomputable def row (s code : V) : V := by
  classical
  let tag := code % 4
  let payload := code / 4
  let a := ArithmeticCantor.first payload
  let b := ArithmeticCantor.second payload
  exact if code = 0 then zeroFormula else
    if tag = 0 then imp ℒₛₑₜ (znth s a) (znth s b) else
    if tag = 1 then atomCode 1 a b else
    if tag = 2 then namedAll ℒₛₑₜ a (znth s b) else atomCode 0 a b

def rowDef : 𝚺₁.Semisentence 3 := .mkSigma “out s code.
  (code = 0 ∧ !zeroFormulaDef out) ∨ (code ≠ 0 ∧
    ∃ tag, !remDef tag code 4 ∧ ∃ payload, !divDef payload code 4 ∧
    ∃ a, !ArithmeticCantor.firstDef a payload ∧ ∃ b, !ArithmeticCantor.secondDef b payload ∧
    ((tag = 0 ∧ ∃ left, !znthDef left s a ∧ ∃ right, !znthDef right s b ∧
        !(impGraph ℒₛₑₜ) out left right) ∨
     (tag = 1 ∧ !atomCodeDef out 1 a b) ∨
     (tag = 2 ∧ ∃ body, !znthDef body s b ∧ !(namedAllDef ℒₛₑₜ) out a body) ∨
     (tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ !atomCodeDef out 0 a b)))”
instance row_defined : 𝚺₁-Function₂[V] row via rowDef := .mk fun e => by
  classical
  by_cases hz : e 2 = 0
  · simp [rowDef,row,hz]
  · by_cases h0 : e 2 % 4 = 0
    · simp [rowDef,row,hz,h0]
    · by_cases h1 : e 2 % 4 = 1
      · simp [rowDef,row,hz,h1]
      · by_cases h2 : e 2 % 4 = 2 <;> simp [rowDef,row,hz,h0,h1,h2]

@[simp] lemma row_zero (s : V) : row s 0 = zeroFormula := by simp [row]

/-- Local consequences of Foundation Seq's actual append membership laws.
These avoid importing an unrelated proof-evaluator module for its wrappers. -/
private lemma znth_append_old {s : V} (hs : Seq s) (x i : V) (hi : i < lh s) :
    znth (seqCons s x) i = znth s i := by
  apply (hs.seqCons x).znth_eq_of_mem
  exact Seq.subset_seqCons s x (hs.znth hi)
private lemma znth_append_last {s : V} (hs : Seq s) (x : V) :
    znth (seqCons s x) (lh s) = x :=
  (hs.seqCons x).znth_eq_of_mem (Seq.mem_seqCons s x)
@[simp] private lemma znth_singleton (x : V) : znth (seqCons ∅ x) 0 = x := by
  simpa only [lh_empty] using znth_append_last (seq_empty (V := V)) x

namespace History

def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “out. ∃ t, !zeroFormulaDef t ∧ !mkSeq₁Def out t”
  succ := .mkSigma “out previous index. ∃ t, !rowDef t previous (index+1) ∧
    !seqConsDef out previous t”
noncomputable def construction : PR.Construction V blueprint where
  zero _ := seqCons ∅ zeroFormula
  succ _ index previous := seqCons previous (row previous (index+1))
  zero_defined := .mk fun e => by simp [blueprint]
  succ_defined := .mk fun e => by simp [blueprint]

end History

noncomputable def history (code : V) : V := History.construction.result ![] code
def historyDef : 𝚺₁.Semisentence 2 := History.blueprint.resultDef
instance history_defined : 𝚺₁-Function₁[V] history via historyDef := .mk fun e => by
  have h := (History.construction (V := V)).result_defined.df e
  have he : (fun i : Fin 0 => e i.succ.succ) = ![] := Subsingleton.elim _ _
  change History.blueprint.resultDef.val.Evalb e ↔
    e 0 = History.construction.result (fun i : Fin 0 => e i.succ.succ) (e 1) at h
  rw [he] at h
  exact h
private instance history_delta : 𝚫₁-Function₁[V] history :=
  history_defined.graph_delta.to_definable
@[simp] lemma history_zero : history (0 : V) = seqCons ∅ zeroFormula := by
  simp [history,History.construction]
@[simp] lemma history_succ (code : V) :
    history (code+1) = seqCons (history code) (row (history code) (code+1)) := by
  simp [history,History.construction]
lemma history_seq (code : V) : Seq (history code) := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih =>
    rw [history_succ]
    exact ih.seqCons _
lemma history_length (code : V) : lh (history code) = code+1 := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih => rw [history_succ,(history_seq code).lh_seqCons,ih]

noncomputable def decode (code : V) : V := znth (history code) code
def decodeDef : 𝚺₁.Semisentence 2 := .mkSigma “out code.
  ∃ s, !historyDef s code ∧ !znthDef out s code”
instance decode_defined : 𝚺₁-Function₁[V] decode via decodeDef :=
  .mk fun e => by simp [decodeDef,decode]
private instance decode_delta : 𝚫₁-Function₁[V] decode :=
  decode_defined.graph_delta.to_definable

lemma history_lookup_le (code : V) : ∀ i ≤ code, znth (history code) i = decode i := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro i hi
    have hi0 : i = 0 := le_antisymm hi (by simp)
    subst i
    rfl
  case succ code ih =>
    intro i hi
    by_cases he : i = code+1
    · subst i
      rfl
    · have hil : i < code+1 := lt_of_le_of_ne hi he
      rw [history_succ,znth_append_old (history_seq code) _ i
        (by simpa only [history_length] using hil)]
      exact ih i (lt_succ_iff_le.mp hil)
lemma history_lookup (code i : V) :
    znth (history code) i = if i ≤ code then decode i else 0 := by
  classical
  by_cases hi : i ≤ code
  · simp only [hi,if_pos]
    exact history_lookup_le code i hi
  · simp only [hi,if_false]
    apply znth_prop_not
    right
    rw [history_length]
    exact lt_iff_succ_le.mp (lt_of_not_ge hi)
@[simp] lemma decode_zero : decode (0 : V) = zeroFormula := by
  simp [decode,history_zero]
lemma decode_succ_row (raw : V) : decode (raw+1) = row (history raw) (raw+1) := by
  unfold decode
  rw [history_succ]
  simpa only [history_length] using
    znth_append_last (history_seq raw) (row (history raw) (raw+1))

/-- Every child read by a positive implication/universal row is already stored. -/
lemma child_bounds {code : V} (hc : 0 < code) :
    ArithmeticCantor.first (code/4) < code ∧ ArithmeticCantor.second (code/4) < code := by
  have hd : code/4 < code := div_lt_of_pos_of_one_lt hc (by simp)
  exact ⟨lt_of_le_of_lt (ArithmeticCantor.projections_spec _).1 hd,
    lt_of_le_of_lt (ArithmeticCantor.projections_spec _).2.1 hd⟩

lemma row_isFormula (s code : V)
    (hs : ∀ i < code, IsFormula ℒₛₑₜ (znth s i)) : IsFormula ℒₛₑₜ (row s code) := by
  classical
  by_cases hz : code = 0
  · simp [row,hz,zeroFormula_isFormula]
  · have hpos : 0 < code := lt_of_le_of_ne (by simp) (Ne.symm hz)
    have ha := hs _ (child_bounds hpos).1
    have hb := hs _ (child_bounds hpos).2
    by_cases h0 : code%4 = 0
    · simpa [row,hz,h0] using IsSemiformula.imp.mpr ⟨ha,hb⟩
    · by_cases h1 : code%4 = 1
      · simpa [row,hz,h0,h1] using memCode_isFormula (V := V) (ArithmeticCantor.first (code/4)) (ArithmeticCantor.second (code/4))
      · by_cases h2 : code%4 = 2
        · simpa [row,hz,h0,h1,h2] using namedAll_isFormula hb (ArithmeticCantor.first (code/4))
        · simpa [row,hz,h0,h1,h2] using eqCode_isFormula (V := V) (ArithmeticCantor.first (code/4)) (ArithmeticCantor.second (code/4))

/-- A bounded internal prefix, rather than an external well-founded recursion. -/
lemma history_formulas (code : V) :
    ∀ i ≤ code, IsFormula ℒₛₑₜ (znth (history code) i) := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro i hi
    have hi0 : i = 0 := le_antisymm hi (by simp)
    subst i
    simpa using zeroFormula_isFormula (V := V)
  case succ code ih =>
    intro i hi
    by_cases he : i = code+1
    · subst i
      have hv := row_isFormula (history code) (code+1) (by
        intro j hj
        exact ih j (lt_succ_iff_le.mp hj))
      change IsFormula ℒₛₑₜ (decode (code+1))
      rw [decode_succ_row]
      exact hv
    · have hil : i < code+1 := lt_of_le_of_ne hi he
      rw [history_succ,znth_append_old (history_seq code) _ i
        (by simpa only [history_length] using hil)]
      exact ih i (lt_succ_iff_le.mp hil)

theorem decode_isFormula (code : V) : IsFormula ℒₛₑₜ (decode code) :=
  history_formulas code code le_rfl

/-- The exact positive recurrence; source zero remains a separately defined alias. -/
theorem decode_succ (raw : V) :
    decode (raw+1) =
      if (raw+1)%4 = 0 then
        imp ℒₛₑₜ (decode (ArithmeticCantor.first ((raw+1)/4))) (decode (ArithmeticCantor.second ((raw+1)/4)))
      else if (raw+1)%4 = 1 then atomCode 1 (ArithmeticCantor.first ((raw+1)/4)) (ArithmeticCantor.second ((raw+1)/4))
      else if (raw+1)%4 = 2 then namedAll ℒₛₑₜ (ArithmeticCantor.first ((raw+1)/4)) (decode (ArithmeticCantor.second ((raw+1)/4)))
      else atomCode 0 (ArithmeticCantor.first ((raw+1)/4)) (ArithmeticCantor.second ((raw+1)/4)) := by
  have hb := child_bounds (V := V) (code := raw+1) (by simp)
  rw [decode_succ_row]
  simp only [row,show raw+1 ≠ 0 by simp,if_false]
  rw [history_lookup_le raw _ (lt_succ_iff_le.mp hb.1),
    history_lookup_le raw _ (lt_succ_iff_le.mp hb.2)]

end LeanProofs.ZFCinPA.ModelCodedDecoder254
