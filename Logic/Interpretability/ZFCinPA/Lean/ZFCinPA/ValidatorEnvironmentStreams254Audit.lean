import ZFCinPA.ValidatorEnvironmentStreams254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
open LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_sigma1
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.streamEnv_of_lt
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.streamFree_of_bounds
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.apart_of_mod_ne
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.bound_lt_alternateStart
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.one_lt_alternateStart
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_mod_ne
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_apart
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_env
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_free
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.alternateStart_resources
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.encode_formula_relabel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254.encode_formula_next

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (bound seed : V) : alternateStartDef.val.Evalb ![alternateStart bound seed,bound,seed] := by simp
example (bound seed : V) : ∃! out : V, alternateStartDef.val.Evalb ![out,bound,seed] := by simp
example : alternateStart (0 : V) 0=5 := by simp [alternateStart] <;> ring
example : alternateStart (0 : V) 1=4 := by simp [alternateStart] <;> ring
example (s B : V) (hB : B<s) : StreamEnv s B := streamEnv_of_lt hB
example (s F : V) (hF : F<s) (h1 : 1<s) : StreamFree s F := streamFree_of_bounds hF h1
example (s t : V) (h : s % 2≠t % 2) : Apart s t := apart_of_mod_ne h
example (bound seed : V) : bound<alternateStart bound seed := bound_lt_alternateStart bound seed
example (bound seed : V) : 1<alternateStart bound seed := one_lt_alternateStart bound seed
example (bound seed : V) : seed % 2≠alternateStart bound seed % 2 := alternateStart_mod_ne bound seed
example (bound seed : V) : Apart seed (alternateStart bound seed) := alternateStart_apart bound seed
example (bound seed B : V) (hB : B≤bound) : StreamEnv (alternateStart bound seed) B :=
  alternateStart_env bound seed B hB
example (bound seed F : V) (hF : F≤bound) : StreamFree (alternateStart bound seed) F :=
  alternateStart_free bound seed F hF
example (F B B' seed : V) :
    StreamFree (alternateStart (F+B+B') seed) F ∧
    StreamEnv (alternateStart (F+B+B') seed) B ∧
    StreamEnv (alternateStart (F+B+B') seed) B' ∧ Apart seed (alternateStart (F+B+B') seed) :=
  alternateStart_resources F B B' seed

section Higher
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
example (p F s t : V) (hp : IsFormula ℒₛₑₜ p) (hs : StreamFree s F) (ht : StreamFree t F) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) := encode_formula_relabel hp F s t hs ht
example (p F s : V) (hp : IsFormula ℒₛₑₜ p) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s p) (encode F 0 (s+2) p)) ∧
    CProv (wim (encode F 0 (s+2) p) (encode F 0 s p)) := encode_formula_next hp F s hs
example (p : V) (hp : IsFormula ℒₛₑₜ p) :
    CProv (wim (encode 0 0 2 p) (encode 0 0 4 p)) ∧
    CProv (wim (encode 0 0 4 p) (encode 0 0 2 p)) :=
  encode_formula_relabel hp 0 2 4 (streamFree_of_bounds (by simp) (by simp))
    (streamFree_of_bounds (by simp) (by simp))
example (p F s t : V) (hp : IsFormula ℒₛₑₜ p) (hs : StreamFree s F) (ht : StreamFree t F)
    (hproof : CProv (encode F 0 s p)) : CProv (encode F 0 t p) :=
  cProv_mp (encode_formula_relabel hp F s t hs ht).1 hproof
end Higher
