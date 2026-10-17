import ZFCinPA.ValidatorProvability254
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ArithmeticHistory254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
open LeanProofs.ZFCinPA.ValidatorProvability254
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_defined
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_definable
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_truth
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_mp
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_gen
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho1
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho2
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho3
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho4
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho5
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho6
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho7
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_rho8
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_bundle
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_implicational
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_k
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_s
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_peirce
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_composition
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_ex_falso
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_classical
#print axioms LeanProofs.ZFCinPA.ValidatorProvability254.cProv_nat_iff
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (n : V) : cProvDef.val.Evalb ![n] ↔ ∃ d : V, value d=n+1 := by simp [CProv]
example : CProv (0 : V) := cProv_truth
example (a b : V) (hi : CProv (wim a b)) (ha : CProv a) : CProv b := cProv_mp hi ha
example (a p : V) (hp : CProv p) : CProv (wal a p) := cProv_gen a hp
example (a b : V) : CProv (rho1 a b) := cProv_rho1 a b
example (a b c : V) : CProv (rho2 a b c) := cProv_rho2 a b c
example (a b c : V) : CProv (rho3 a b c) := cProv_rho3 a b c
example (a b c : V) : CProv (rho4 a b c) := cProv_rho4 a b c
example (a b c : V) : CProv (rho5 a b c) := cProv_rho5 a b c
example (a b : V) : CProv (rho6 a b) := cProv_rho6 a b
example (a b c : V) : CProv (rho7 a b c) := cProv_rho7 a b c
example (a b c u : V) : CProv (rho8 a b c u) := cProv_rho8 a b c u
example (a b c : V) (hca : c≠a) (hcb : c≠b) : CProv (bundle a b c) := cProv_bundle a b c hca hcb
example : Kalmar.Classical (wim : V → V → V) 1 CProv := cProv_classical
example : CProv (wim (1 : V) 0) := cProv_ex_falso 0
example (n : Nat) : CProv (V := Nat) n ↔ Code254.C254 n := cProv_nat_iff n
