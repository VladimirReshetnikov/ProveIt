import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAFixSuccWitnessBound
import DiophantineConsistency.PRAFstIdxWitnessBound
import DiophantineConsistency.PRARewritingWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Bind the fst-index witness in the actual derivation sigma core.
    The bounded formula-set graph and ten-rule tail remain explicit premises. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRADerivationCoreSigmaBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable] (T : Theory L) [T.Δ₁]
noncomputable def coreLeft : ArithmeticSemisentence 2 :=
  “d C. ∃ fst, !fstIdxDef fst d ∧ !(isFormulaSet L).sigma fst”
noncomputable def coreTail : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with
  | .and _ tail => tail
  | _ => ⊥
theorem core_shape : (Derivation.blueprint T).core.sigma.val = (coreLeft (L := L)) ⋏ coreTail T := by
  rfl
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem fst_le (x p : V) : fstIdxDef.val.Evalb ![x,p] → x ≤ p := by
  intro h
  simp [fstIdxDef, pi₁Def] at h
  rcases h with ⟨b,_,hb⟩
  have hx : x ≤ p-1 := by rw [hb]; exact le_pair_left x b
  exact le_trans hx (by simp)

noncomputable def setInsideCore : ArithmeticSemisentence 3 :=
  “fst d C. !(isFormulaSet L).sigma fst”

theorem coreLeft_bound (d C fst w : V) (hw : d+1 ≤ w)
    (hfst : fstIdxDef.val.Evalb ![fst,d])
    (hset : (bnd (setInsideCore (L := L))).Evalb ![fst,d,C,w]) :
    (bnd (coreLeft (L := L))).Evalb ![d,C,w] := by
  simp [coreLeft,bnd]
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hle : fst ≤ d := fst_le fst d hfst
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
  have hf : (ω ▹ fstIdxDef.val).Evalb ![fst,d,C] := by
    simpa [ω, Semiformula.eval_substs] using hfst
  have hw' : ((ω #1).val ![fst,d,C] Empty.elim) + 1 ≤ w := by
    simpa [ω] using hw
  have hb := PRARewritingWitnessBound.binary_rew_bound_with fstIdxDef.val
    (fun _ d => d+1) PRAFstIdxWitnessBound.fstIdx_bnd_succ ω ![fst,d,C] w hw' hf
  exact ⟨fst, lt_of_lt_of_le (lt_succ_iff_le.mpr hle) hw, by simpa using hb, hset⟩

theorem derivationCoreSigma_bound (d C fst w : V) (hw : d+1 ≤ w)
    (hfst : fstIdxDef.val.Evalb ![fst,d])
    (hset : (bnd (setInsideCore (L := L))).Evalb ![fst,d,C,w])
    (htail : (bnd (coreTail T)).Evalb ![d,C,w]) :
    (bnd (Derivation.blueprint T).core.sigma.val).Evalb ![d,C,w] := by
  rw [core_shape T]
  simp only [bnd, LogicalConnective.HomClass.map_and]
  exact ⟨coreLeft_bound d C fst w hw hfst hset,htail⟩
noncomputable def boundedSetInsideCore : ArithmeticSemisentence 4 := bnd (setInsideCore (L := L))
noncomputable def boundedCoreTail : ArithmeticSemisentence 3 := bnd (coreTail T)
noncomputable def boundedCoreSigma : ArithmeticSemisentence 3 := bnd (Derivation.blueprint T).core.sigma.val
noncomputable def coreSigmaBoundBody : ArithmeticSemisentence 4 :=
  “d C fst w. d+1 ≤ w ∧ !fstIdxDef fst d ∧ !((boundedSetInsideCore (L := L))) fst d C w ∧
    !((boundedCoreTail T)) d C w → !((boundedCoreSigma T)) d C w”

theorem coreSigmaBoundBody_model (e : Fin 4 → V) : (coreSigmaBoundBody T).Eval e Empty.elim := by
  simp [coreSigmaBoundBody, boundedSetInsideCore, boundedCoreTail, boundedCoreSigma, Semiformula.eval_substs]
  exact derivationCoreSigma_bound T (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def coreSigmaBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (coreSigmaBoundBody T)

theorem candidate_proves_coreSigma_bound : PRA ⊢ coreSigmaBoundSentence T := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact coreSigmaBoundBody_model T e
end DiophantineConsistency.PRADerivationCoreSigmaBound
