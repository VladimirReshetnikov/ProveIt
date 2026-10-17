import ZFCinPA.ValidatorEnvironmentAlpha254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254
open LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.streamFree_next
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.streamEnv_cons_next
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.freshPair_next
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.cross_body_vac
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.eqUnder_refl
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.contra_under
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.eqUnder_neg
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.imp_under
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.eqUnder_imp
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.eqUnder_conj
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.reverse_eq_premise
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.eqUnder_all_of_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.eqUnder_ex_of_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.term_eq_under
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.atom_eq_under
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.encoded_binder_steps
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.encode_eq_under
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254.encode_formula_alpha

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (s F : V) (h : StreamFree s F) : StreamFree (s+2) F := streamFree_next h
example (s B x : V) (h : StreamEnv s B) (hx : ∀ k : V, (s+2)+2*k≠x) :
    StreamEnv (s+2) (x∷B) := streamEnv_cons_next h hx
example (F B B' s t : V) (h : FreshPair F B B' s t) :
    FreshPair F (s∷B) (t∷B') (s+2) (t+2) := freshPair_next h
example (h p : V) : EqUnder h p p := eqUnder_refl h p
example (h p q : V) (hpq : CProv (wim h (wim p q))) :
    CProv (wim h (wim (wim q 1) (wim p 1))) := contra_under hpq
example (h p q : V) (he : EqUnder h p q) : EqUnder h (wim p 1) (wim q 1) := eqUnder_neg he
example (h p p' q q' : V) (hp : CProv (wim h (wim p' p)))
    (hq : CProv (wim h (wim q q'))) :
    CProv (wim h (wim (wim p q) (wim p' q'))) := imp_under hp hq
example (h p p' q q' : V) (hp : EqUnder h p p') (hq : EqUnder h q q') :
    EqUnder h (wim p q) (wim p' q') := eqUnder_imp hp hq
example (h p p' q q' : V) (hp : EqUnder h p p') (hq : EqUnder h q q') :
    EqUnder h (conj p q) (conj p' q') := eqUnder_conj hp hq
example (h r x y : V) (hr : CProv (wim h (wim (weq x y) r))) :
    CProv (wim h (wim (weq y x) r)) := reverse_eq_premise hr
example (B B' p q x y : V) (hb : EqUnder (eqContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eqContext B B')) (vyh : Vac y (eqContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) : EqUnder (eqContext B B') (wal x p) (wal y q) :=
  eqUnder_all_of_cons B B' p q x y hb vxh vyh vxq vyp
example (B B' p q x y : V) (hb : EqUnder (eqContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eqContext B B')) (vyh : Vac y (eqContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) : EqUnder (eqContext B B') (ex x p) (ex y q) :=
  eqUnder_ex_of_cons B B' p q x y hb vxh vyh vxq vyp
example (n u F B B' : V) (hu : IsSemiterm ℒₛₑₜ n u) (hB : len B=n) :
    CProv (wim (eqContext B B') (weq (TermLabels.term F B u) (TermLabels.term F B' u))) :=
  term_eq_under hu F B B' hB
example (n arity R terms F B B' s t : V) (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (hB : len B=n) :
    EqUnder (eqContext B B') (Formulas.atom ?[F,B,s] arity R terms)
      (Formulas.atom ?[F,B',t] arity R terms) := atom_eq_under hr ht F B B' s t hB

section Higher
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
example (n p F B B' s t : V) (hp : IsSemiformula ℒₛₑₜ (n+1) p)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    Vac s (encode F (t∷B') (t+2) p) ∧ Vac t (encode F (s∷B) (s+2) p) :=
  cross_body_vac hp F B B' s t hB hB' hf
example (n p F B B' s t : V) (hp : IsSemiformula ℒₛₑₜ (n+1) p)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t)
    (ih : EqUnder (eqContext (s∷B) (t∷B'))
      (encode F (s∷B) (s+2) p) (encode F (t∷B') (t+2) p)) :
    EqUnder (eqContext B B') (encode F B s (^∀ p)) (encode F B' t (^∀ p)) ∧
    EqUnder (eqContext B B') (encode F B s (^∃ p)) (encode F B' t (^∃ p)) :=
  encoded_binder_steps hp F B B' s t hB hB' hf ih
example (n p F B B' s t : V) (hp : IsSemiformula ℒₛₑₜ n p)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    EqUnder (eqContext B B') (encode F B s p) (encode F B' t p) :=
  encode_eq_under hp F B B' s t hB hB' hf
example (n p F B B' s t : V) (hp : IsSemiformula ℒₛₑₜ n p)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    CProv (wim (eqContext B B') (wim (encode F B s p) (encode F B' t p))) :=
  (encode_eq_under hp F B B' s t hB hB' hf).1
example (n p F B B' s t : V) (hp : IsSemiformula ℒₛₑₜ n p)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    CProv (wim (eqContext B B') (wim (encode F B' t p) (encode F B s p))) :=
  (encode_eq_under hp F B B' s t hB hB' hf).2
example (p F s t : V) (hp : IsFormula ℒₛₑₜ p)
    (hs : StreamFree s F) (ht : StreamFree t F) (hap : Apart s t) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) := encode_formula_alpha hp F s t hs ht hap
example (n p F B B' s t : V) (hp : IsSemiformula ℒₛₑₜ (n+1) p)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    EqUnder (eqContext (s∷B) (t∷B'))
      (encode F (s∷B) (s+2) p) (encode F (t∷B') (t+2) p) :=
  encode_eq_under hp F (s∷B) (t∷B') (s+2) (t+2)
    (by simp [hB]) (by simp [hB']) (freshPair_next hf)
example (p F s t : V) (hp : IsFormula ℒₛₑₜ p)
    (hs : StreamFree s F) (ht : StreamFree t F) (hap : Apart s t)
    (hproof : CProv (encode F 0 s p)) : CProv (encode F 0 t p) :=
  cProv_mp (encode_formula_alpha hp F s t hs ht hap).1 hproof
end Higher
