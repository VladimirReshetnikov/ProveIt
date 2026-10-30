import DiophantineConsistency.PRAFixSuccWitnessBound
import DiophantineConsistency.PRAFstIdxWitnessBound
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
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, coreSigmaBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact coreSigmaBoundBody_model T e
end DiophantineConsistency.PRADerivationCoreSigmaBound
