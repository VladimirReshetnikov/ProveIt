import ZFCinPA.ValidatorEnvironmentVacuity254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.avoid_nil
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.avoid_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.free_label_avoids
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.stream_head
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.stream_next
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.stream_of_lt
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.term_label_avoids
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.atom_vac
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.encode_vac
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254.encode_formula_vac

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (z : V) : Avoid z (0 : V) := avoid_nil z
example (z B x : V) (hB : Avoid z B) (hx : z≠x) : Avoid z (x∷B) := avoid_cons hB hx
example (z F i : V) (hF : FreeAvoid z F) : z≠freeLabel F i := free_label_avoids hF i
example (z F : V) (hF : FreeAvoid z F) : z≠1 := hF.1
example (z fresh : V) (hs : StreamAvoid z fresh) : z≠fresh := stream_head hs
example (z fresh : V) (hs : StreamAvoid z fresh) : StreamAvoid z (fresh+2) := stream_next hs
example (z fresh : V) (hz : z<fresh) : StreamAvoid z fresh := stream_of_lt hz
example (z B fresh : V) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    Avoid z (fresh∷B) ∧ StreamAvoid z (fresh+2) :=
  ⟨avoid_cons hB (stream_head hs),stream_next hs⟩
example (n t F B z : V) (ht : IsSemiterm ℒₛₑₜ n t) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) : z≠TermLabels.term F B t :=
  term_label_avoids ht F B z hlen hF hB
example (n arity R terms F B fresh z : V) (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) :
    Vac z (Formulas.atom ?[F,B,fresh] arity R terms) :=
  atom_vac hr ht F B fresh z hlen hF hB

section Higher
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
example (n p F B fresh z : V) (hp : IsSemiformula ℒₛₑₜ n p) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    Vac z (encode F B fresh p) := encode_vac hp F B fresh z hlen hF hB hs
example (n p F B fresh z : V) (hp : IsSemiformula ℒₛₑₜ n p) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    CProv (wim (encode F B fresh p) (wal z (encode F B fresh p))) :=
  encode_vac hp F B fresh z hlen hF hB hs
example (p F fresh z : V) (hp : IsFormula ℒₛₑₜ p)
    (hF : FreeAvoid z F) (hs : StreamAvoid z fresh) :
    Vac z (encode F 0 fresh p) := encode_formula_vac hp F fresh z hF hs
example (p : V) (hp : IsFormula ℒₛₑₜ p) : Vac (0 : V) (encode 0 0 2 p) :=
  encode_formula_vac hp 0 2 0 ⟨by simp,avoid_nil 0⟩ (stream_of_lt (by simp))
example (n p F B fresh z : V) (hp : IsSemiformula ℒₛₑₜ (n+1) p)
    (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    Vac z (encode F (fresh∷B) (fresh+2) p) :=
  encode_vac hp F (fresh∷B) (fresh+2) z (by simp [hlen]) hF
    (avoid_cons hB (stream_head hs)) (stream_next hs)
example (n p F B fresh z : V) (hp : IsSemiformula ℒₛₑₜ (n+1) p)
    (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    Vac z (encode F B fresh (^∀ p)) :=
  encode_vac (by simpa using hp) F B fresh z hlen hF hB hs
end Higher
