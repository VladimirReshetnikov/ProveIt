import ZFCinPA.ValidatorLabelAvoidance
import ZFCinPA.ValidatorEnvironmentAlpha222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-!
Concrete internal fresh-stream selection and composition of actual C222 alpha
transport. The fixed Σ0 selector and formula transport (through the Alpha222
theorem) both use IΣ1. No CProv254 semantics are used. A coarse
bound by the numeric vector code suffices for every stored label. The fixed selector chooses the opposite parity above that bound. The
formula client compares arbitrary free-safe starts, including overlapping
streams. Original-stream safety remains explicit; source substitution,
semantic quantifier inference and proof translation are not asserted.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentStreams222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEnvironmentAlpha222
open scoped LO.FirstOrder.Arithmetic

/-- Graph argument order is output, coarse bound, original stream seed. -/
def alternateStartDef : 𝚺₀.Semisentence 3 := ValidatorLabelAvoidance.alternateStartDef

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def alternateStart (bound seed : V) : V := by
  classical
  exact if seed % 2=0 then 2*(bound+2)+1 else 2*(bound+2)

instance alternateStart_defined : 𝚺₀-Function₂[V] alternateStart via alternateStartDef :=
  ValidatorLabelAvoidance.alternateStartGraph

instance alternateStart_sigma1 : 𝚺₁-Function₂[V] alternateStart :=
  alternateStart_defined.to_definable₀

lemma streamEnv_of_lt {s B : V} (hB : B<s) : StreamEnv s B :=
  ValidatorLabelAvoidance.streamEnv_of_lt hB
lemma streamFree_of_bounds {s F : V} (hF : F<s) (h1 : 1<s) : StreamFree s F :=
  ValidatorLabelAvoidance.streamFree_of_bounds hF h1
lemma apart_of_mod_ne {s t : V} (h : s % 2≠t % 2) : Apart s t :=
  ValidatorLabelAvoidance.apart_of_mod_ne h
lemma bound_lt_alternateStart (bound seed : V) : bound<alternateStart bound seed :=
  ValidatorLabelAvoidance.bound_lt_alternateStart bound seed
lemma one_lt_alternateStart (bound seed : V) : 1<alternateStart bound seed :=
  ValidatorLabelAvoidance.one_lt_alternateStart bound seed
lemma alternateStart_mod_ne (bound seed : V) : seed % 2≠alternateStart bound seed % 2 :=
  ValidatorLabelAvoidance.alternateStart_mod_ne bound seed
lemma alternateStart_apart (bound seed : V) : Apart seed (alternateStart bound seed) :=
  ValidatorLabelAvoidance.alternateStart_apart bound seed
lemma alternateStart_env (bound seed B : V) (hB : B≤bound) :
    StreamEnv (alternateStart bound seed) B :=
  ValidatorLabelAvoidance.alternateStart_env bound seed B hB
lemma alternateStart_free (bound seed F : V) (hF : F≤bound) :
    StreamFree (alternateStart bound seed) F :=
  ValidatorLabelAvoidance.alternateStart_free bound seed F hF
/-- A concrete stream avoiding the free labels, fallback and both bound stacks. -/
lemma alternateStart_resources (F B B' seed : V) :
    StreamFree (alternateStart (F+B+B') seed) F ∧
    StreamEnv (alternateStart (F+B+B') seed) B ∧
    StreamEnv (alternateStart (F+B+B') seed) B' ∧
    Apart seed (alternateStart (F+B+B') seed) :=
  ValidatorLabelAvoidance.alternateStart_resources F B B' seed

/-- Compare arbitrary free-safe starts. When their residues agree, compose
through the explicit fresh stream of the opposite parity. -/
theorem encode_formula_relabel {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s t : V) (hs : StreamFree s F) (ht : StreamFree t F) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) :=
  ValidatorLabelAvoidance.stream_relabel
    (R := fun a b => CProv (wim (encode F 0 a p) (encode F 0 b p))) F s t
    (fun h₁ h₂ => compose h₁ h₂)
    (fun a b ha hb hab => encode_formula_alpha hp F a b ha hb hab) hs ht

/-- The overlapping next-stream case needed after one binder allocation. -/
lemma encode_formula_next {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s p) (encode F 0 (s+2) p)) ∧
    CProv (wim (encode F 0 (s+2) p) (encode F 0 s p)) :=
  encode_formula_relabel hp F s (s+2) hs (streamFree_next hs)

end LeanProofs.ZFCinPA.ValidatorEnvironmentStreams222
