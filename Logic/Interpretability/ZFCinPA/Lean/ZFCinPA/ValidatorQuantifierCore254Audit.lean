import ZFCinPA.ValidatorQuantifierCore254

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.compose
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.contrapose
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.contrapose_of
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.double_neg_elim
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.double_neg_intro
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.all_distribution
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.all_swap
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.ex_all_elim
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.ex_equality
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.all_mono
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.ex_mono
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.ex_elim_of_vac
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_neg
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.conj_left
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.conj_right
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.conj_intro
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_rel
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_eq
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_truth
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_falsum
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_imp
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.vac_all
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.all_imp_ex
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.all_under_two
#print axioms LeanProofs.ZFCinPA.ValidatorQuantifierCore254.all_relational

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (i p q : V) (h : CProv (wim p q)) :
    CProv (wim (wal i p) (wal i q)) := all_mono i h
example (i p q : V) (h : CProv (wim p q)) :
    CProv (wim (ex i p) (ex i q)) := ex_mono i h
example (i p : V) (h : Vac i p) : CProv (wim (ex i p) p) := ex_elim_of_vac h
example (i p : V) (h : Vac i p) : Vac i (neg p) := vac_neg h
example (i a b : V) (ha : Vac i a) (hb : Vac i b) :
    Vac i (wim a b) := vac_imp ha hb
example (i j p : V) (hp : Vac i p) : Vac i (wal j p) := vac_all j hp
example (a b i : V) (ha : i≠a) (hb : i≠b) :
    CProv (wim (wel a b) (wal i (wel a b))) := vac_rel a b i ha hb
example (a b i : V) (ha : i≠a) (hb : i≠b) :
    CProv (wim (weq a b) (wal i (weq a b))) := vac_eq a b i ha hb
example (i : V) (hi : i≠0) : Vac i (wel (0 : V) 0) := vac_rel 0 0 i hi hi
example (i : V) (hi : i≠0) : Vac i (weq (0 : V) 0) := vac_eq 0 0 i hi hi
example : Vac (0 : V) 0 := vac_truth 0
example : Vac (0 : V) 1 := vac_falsum 0
example (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (ex i p) (ex i q))) := all_imp_ex i p q
example (i h p q : V) (hh : Vac i h) (hp : Vac i p)
    (hpq : CProv (wim h (wim p q))) :
    CProv (wim h (wim p (wal i q))) := all_under_two i hpq hh hp
example (h p q x y : V) (hpq : CProv (wim h (wim (weq x y) (wim p q))))
    (vxh : Vac x h) (vxq : Vac x q) (vyh : Vac y h) (vyall : Vac y (wal x p)) :
    CProv (wim h (wim (wal x p) (wal y q))) :=
  all_relational h p q x y hpq vxh vxq vyh vyall
example (h p q x : V) (hpq : CProv (wim h (wim (weq x x) (wim p q))))
    (vxh : Vac x h) (vxq : Vac x q) (vxall : Vac x (wal x p)) :
    CProv (wim h (wim (wal x p) (wal x q))) :=
  all_relational h p q x x hpq vxh vxq vxh vxall
example (p q x y : V) (hpq : CProv (wim (0 : V) (wim (weq x y) (wim p q))))
    (vxq : Vac x q) (vyall : Vac y (wal x p)) :
    CProv (wim (0 : V) (wim (wal x p) (wal y q))) :=
  all_relational 0 p q x y hpq (vac_truth x) vxq (vac_truth y) vyall
example (a b : V) (ha : CProv a) (hb : CProv b) : CProv (conj a b) := conj_intro ha hb
