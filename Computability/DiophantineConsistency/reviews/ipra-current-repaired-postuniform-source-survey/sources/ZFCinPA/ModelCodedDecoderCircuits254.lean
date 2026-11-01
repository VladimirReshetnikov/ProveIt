import ZFCinPA.ModelCodedDecoderRho6_254
import ZFCinPA.ModelCodedDecoderEquality254

set_option autoImplicit false

/-!
Interpret every fixed finite constructor circuit at arbitrary internal inputs.
The live relative-falsity code is replaced by Bottom only up to provable
equivalence, including under named binders. Variable labels still use the
original numeric child values; interpreting a formula never changes a label.
The bundle instances identify their logical formulas, not proofs of C or G.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def interpret : Circuit → V → V → V → V → Formula V ℒₛₑₜ
  | .input0, a, _, _, _ => decoded a
  | .input1, _, b, _, _ => decoded b
  | .input2, _, _, c, _ => decoded c
  | .input3, _, _, _, u => decoded u
  | .one, _, _, _, _ => ⊥
  | .node .imp x y, a, b, c, u => interpret x a b c u 🡒 interpret y a b c u
  | .node .rel x y, a, b, c, u =>
      memAtom (Semiterm.fvar (x.eval a b c u)) (Semiterm.fvar (y.eval a b c u))
  | .node .all x y, a, b, c, u => namedFormula (x.eval a b c u) (interpret y a b c u)
  | .node .eq x y, a, b, c, u =>
      eqAtom (Semiterm.fvar (x.eval a b c u)) (Semiterm.fvar (y.eval a b c u))

theorem decoded_one_equiv_bottom (T : InternalTheory V ℒₛₑₜ)
    (hFalse : T ⊢ ∼decoded (1 : V)) : T ⊢ decoded (1 : V) 🡘 ⊥ := by
  classical
  exact E!_intro (N!_iff_CO!.mp hFalse) efq!

/-- Induction is on the fixed external circuit, never on an internal formula.
Each internal input remains arbitrary; target GEN is an explicit resource. -/
theorem decoded_circuit_equiv (T : SetTheory) [T.Δ₁]
    (hFalse : T.internalize V ⊢ ∼decoded (1 : V))
    (hGen : ∀ a p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (e : Circuit) (a b c u : V) :
    T.internalize V ⊢ decoded (e.eval a b c u) 🡘 interpret e a b c u := by
  induction e with
  | input0 => exact ⟨E_Id⟩
  | input1 => exact ⟨E_Id⟩
  | input2 => exact ⟨E_Id⟩
  | input3 => exact ⟨E_Id⟩
  | one => exact decoded_one_equiv_bottom (T.internalize V) hFalse
  | node k x y ihx ihy =>
    cases k with
    | imp =>
      change T.internalize V ⊢
        decoded (ArithmeticCode254.wim (x.eval a b c u) (y.eval a b c u)) 🡘 _
      rw [ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
      exact decoded_imp_congr T _ _ _ _ ihx ihy
    | rel =>
      change T.internalize V ⊢
        decoded (ArithmeticCode254.wel (x.eval a b c u) (y.eval a b c u)) 🡘 _
      rw [decoded_wel]
      exact ⟨E_Id⟩
    | all => exact decoded_all_equiv T (x.eval a b c u) _ (hGen _) _ ihy
    | eq =>
      change T.internalize V ⊢
        decoded (ArithmeticCode254.weq (x.eval a b c u) (y.eval a b c u)) 🡘 _
      rw [decoded_weq]
      exact ⟨E_Id⟩

theorem zf_decoded_circuit_equiv (e : Circuit) (a b c u : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (e.eval a b c u) 🡘 interpret e a b c u :=
  decoded_circuit_equiv 𝗭𝗙 (decoded_one_neg_of_zf 𝗭𝗙 inferInstance)
    (fun a _ hp => zf_provable_namedAll a hp) e a b c u

theorem zfc_decoded_circuit_equiv (e : Circuit) (a b c u : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ decoded (e.eval a b c u) 🡘 interpret e a b c u :=
  decoded_circuit_equiv 𝗭𝗙𝗖
    (decoded_one_neg_of_zf 𝗭𝗙𝗖 (Entailment.WeakerThan.ofSubset Set.subset_union_left))
    (fun a _ hp => zfc_provable_namedAll a hp) e a b c u

theorem zf_decoded_bundleC_equiv (a b c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (bundleC a b c) 🡘 interpret bundleCCircuit a b c 0 :=
  zf_decoded_circuit_equiv bundleCCircuit a b c 0

theorem zf_decoded_bundleG_equiv (a b c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (bundleG a b c) 🡘 interpret bundleGCircuit a b c 0 :=
  zf_decoded_circuit_equiv bundleGCircuit a b c 0

theorem zf_decoded_bundle_equiv (a b c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (bundle a b c) 🡘 interpret bundleCircuit a b c 0 :=
  zf_decoded_circuit_equiv bundleCircuit a b c 0

end LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
