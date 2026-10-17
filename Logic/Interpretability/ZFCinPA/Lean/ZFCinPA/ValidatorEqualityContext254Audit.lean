import ZFCinPA.ValidatorEqualityContext254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_delta
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_delta
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_zero
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_succ
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_nil
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_intro_imp
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_under
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_mono_right
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_interchange
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefix_projection
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_projection
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefix_cons_equiv
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_forward
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_backward
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_head
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_tail
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.discharge_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.under_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContext254.all_of_cons

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (n B B' : V) : prefixContextDef.val.Evalb ![prefixContext n B B',n,B,B'] := by simp
example (n B B' : V) : ∃! out : V, prefixContextDef.val.Evalb ![out,n,B,B'] := by simp
example (B B' : V) : eqContextDef.val.Evalb ![eqContext B B',B,B'] := by simp
example (B B' : V) : ∃! out : V, eqContextDef.val.Evalb ![out,B,B'] := by simp
example (B B' : V) : prefixContext 0 B B'=0 := prefixContext_zero B B'
example (n B B' : V) :
    prefixContext (n+1) B B'=conj (weq B.[n] B'.[n]) (prefixContext n B B') :=
  prefixContext_succ n B B'
example (B' : V) : eqContext (0 : V) B'=0 := eqContext_nil B'
example (a b : V) : CProv (wim a (wim b (conj a b))) := conj_intro_imp a b
example (h a b : V) (ha : CProv (wim h a)) (hb : CProv (wim h b)) :
    CProv (wim h (conj a b)) := conj_under ha hb
example (a b c : V) (h : CProv (wim b c)) :
    CProv (wim (conj a b) (conj a c)) := conj_mono_right a h
example (a b c : V) : CProv (wim (conj a (conj b c)) (conj b (conj a c))) :=
  conj_interchange a b c
example (n B B' i : V) (hi : i<n) :
    CProv (wim (prefixContext n B B') (weq B.[i] B'.[i])) := prefix_projection n B B' i hi
example (B B' i : V) (hi : i<len B) :
    CProv (wim (eqContext B B') (weq B.[i] B'.[i])) := eqContext_projection B B' i hi
example (n B B' x y : V) :
    CProv (wim (prefixContext (n+1) (x∷B) (y∷B')) (conj (weq x y) (prefixContext n B B'))) ∧
    CProv (wim (conj (weq x y) (prefixContext n B B')) (prefixContext (n+1) (x∷B) (y∷B'))) :=
  prefix_cons_equiv n B B' x y
example (B B' x y : V) :
    CProv (wim (eqContext (x∷B) (y∷B')) (conj (weq x y) (eqContext B B'))) :=
  eqContext_cons_forward B B' x y
example (B B' x y : V) :
    CProv (wim (conj (weq x y) (eqContext B B')) (eqContext (x∷B) (y∷B'))) :=
  eqContext_cons_backward B B' x y
example (B B' x y : V) : CProv (wim (eqContext (x∷B) (y∷B')) (weq x y)) :=
  eqContext_cons_head B B' x y
example (B B' x y : V) : CProv (wim (eqContext (x∷B) (y∷B')) (eqContext B B')) :=
  eqContext_cons_tail B B' x y
example (B B' x y p : V) (h : CProv (wim (eqContext (x∷B) (y∷B')) p)) :
    CProv (wim (eqContext B B') (wim (weq x y) p)) := discharge_cons B B' x y h
example (B B' x y p : V) (h : CProv (wim (eqContext B B') (wim (weq x y) p))) :
    CProv (wim (eqContext (x∷B) (y∷B')) p) := under_cons B B' x y h
example : CProv (eqContext (0 : V) 0) := by simpa using (cProv_truth (V := V))
example (B' x y : V) :
    CProv (wim (eqContext (x∷(0 : V)) (y∷B')) (conj (weq x y) 0)) := by
  simpa using eqContext_cons_forward (0 : V) B' x y
example (B i : V) (hi : i<len B) : CProv (wim (eqContext B 0) (weq B.[i] 0)) := by
  simpa using eqContext_projection B 0 i hi
example (B B' p q x y : V)
    (hbody : CProv (wim (eqContext (x∷B) (y∷B')) (wim p q)))
    (vxh : Vac x (eqContext B B')) (vxq : Vac x q)
    (vyh : Vac y (eqContext B B')) (vyall : Vac y (wal x p)) :
    CProv (wim (eqContext B B') (wim (wal x p) (wal y q))) :=
  all_of_cons B B' p q x y hbody vxh vxq vyh vyall
