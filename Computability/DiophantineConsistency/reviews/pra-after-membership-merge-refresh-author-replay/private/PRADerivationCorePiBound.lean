import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAFixSuccWitnessBound
import DiophantineConsistency.PRAFstIdxWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Conditional outer binding for the negative derivation pi core.
    Negative formula-set and rule-tail bounds remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRADerivationCorePiBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable] (T : Theory L) [T.Δ₁]
noncomputable def corePiLeft : ArithmeticSemisentence 2 :=
  “d C. ∀ fst, !fstIdxDef fst d → !(isFormulaSet L).pi fst”
noncomputable def corePiTail : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ tail => tail
  | _ => ⊥
theorem corePi_shape : (Derivation.blueprint T).core.pi.val = (corePiLeft (L := L)) ⋏ corePiTail T := by
  rfl
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem fst_le (x p : V) : fstIdxDef.val.Evalb ![x,p] → x ≤ p := by
  intro h
  simp [fstIdxDef, pi₁Def] at h
  rcases h with ⟨b,_,hb⟩
  have hx : x ≤ p-1 := by rw [hb]; exact le_pair_left x b
  exact le_trans hx (by simp)
noncomputable def negSetInsideCore : ArithmeticSemisentence 3 :=
  “fst d C. ¬!(isFormulaSet L).pi fst”
theorem corePiLeft_neg_bound (d C fst w : V) (hw : d+1 ≤ w)
    (hfst : fstIdxDef.val.Evalb ![fst,d])
    (hset : (bnd (negSetInsideCore (L := L))).Evalb ![fst,d,C,w]) :
    (bnd (∼corePiLeft (L := L))).Evalb ![d,C,w] := by
  simp [corePiLeft, DeMorgan.imply, bnd]
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hle : fst ≤ d := fst_le fst d hfst
  have hb := PRAFstIdxWitnessBound.fstIdx_bnd_succ fst d hfst
  have hs0 : Fin.snoc ![fst,d] (d+1) = ![fst,d,d+1] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hb' := eval_bnd_mono fstIdxDef.val ![fst,d] (Empty.elim : Empty → V) hw (by rw [hs0]; exact hb)
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
  have hn := PRABndRewriting.natural fstIdxDef.val ω ![fst,d,C] w
  have hv : (fun j => (ω #j).val ![fst,d,C] Empty.elim) = ![fst,d] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![fst,d,C] w = ![fst,d,C,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs] at hn
  exact ⟨fst, lt_of_lt_of_le (lt_succ_iff_le.mpr hle) hw, hn.mpr hb', hset⟩
theorem derivationCorePi_neg_bound_of_left (d C fst w : V) (hw : d+1 ≤ w)
    (hfst : fstIdxDef.val.Evalb ![fst,d])
    (hset : (bnd (negSetInsideCore (L := L))).Evalb ![fst,d,C,w]) :
    (bnd (∼(Derivation.blueprint T).core.pi.val)).Evalb ![d,C,w] := by
  rw [corePi_shape T]
  simp only [DeMorgan.and, bnd, LogicalConnective.HomClass.map_or]
  exact Or.inl (corePiLeft_neg_bound d C fst w hw hfst hset)

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem derivationCorePi_neg_bound_of_tail (d C w : V)
    (htail : (bnd (∼corePiTail T)).Evalb ![d,C,w]) :
    (bnd (∼(Derivation.blueprint T).core.pi.val)).Evalb ![d,C,w] := by
  rw [corePi_shape T]
  simp only [DeMorgan.and, bnd, LogicalConnective.HomClass.map_or]
  exact Or.inr htail
noncomputable def boundedNegSetInsideCore : ArithmeticSemisentence 4 := bnd (negSetInsideCore (L := L))
noncomputable def boundedNegCorePi : ArithmeticSemisentence 3 := bnd (∼(Derivation.blueprint T).core.pi.val)
noncomputable def boundedNegCorePiTail : ArithmeticSemisentence 3 := bnd (∼corePiTail T)
noncomputable def corePiLeftBoundBody : ArithmeticSemisentence 4 :=
  “d C fst w. d+1 ≤ w ∧ !fstIdxDef fst d ∧ !((boundedNegSetInsideCore (L := L))) fst d C w → !((boundedNegCorePi T)) d C w”
noncomputable def corePiTailBoundBody : ArithmeticSemisentence 3 :=
  “d C w. !((boundedNegCorePiTail T)) d C w → !((boundedNegCorePi T)) d C w”

theorem corePiLeftBoundBody_model (e : Fin 4 → V) : (corePiLeftBoundBody T).Eval e Empty.elim := by
  simp [corePiLeftBoundBody, boundedNegSetInsideCore, boundedNegCorePi, Semiformula.eval_substs]
  exact derivationCorePi_neg_bound_of_left T (e 0) (e 1) (e 2) (e 3)

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem corePiTailBoundBody_model (e : Fin 3 → V) : (corePiTailBoundBody T).Eval e Empty.elim := by
  simp [corePiTailBoundBody, boundedNegCorePiTail, boundedNegCorePi, Semiformula.eval_substs]
  exact derivationCorePi_neg_bound_of_tail T (e 0) (e 1) (e 2)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def corePiLeftBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (corePiLeftBoundBody T)
noncomputable def corePiTailBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (corePiTailBoundBody T)

theorem candidate_proves_corePiLeft_bound : PRA ⊢ corePiLeftBoundSentence T := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact corePiLeftBoundBody_model T e

theorem candidate_proves_corePiTail_bound : PRA ⊢ corePiTailBoundSentence T := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact corePiTailBoundBody_model T e
end DiophantineConsistency.PRADerivationCorePiBound
