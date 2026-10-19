import ZFCinPA.R2Gic

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.R2Gic.encT_all
#print axioms LeanProofs.ZFCinPA.R2Gic.encT_exs
#print axioms LeanProofs.ZFCinPA.R2Gic.encT_and
#print axioms LeanProofs.ZFCinPA.R2Gic.encT_or
#print axioms LeanProofs.ZFCinPA.R2Gic.encT_imp
#print axioms LeanProofs.ZFCinPA.R2Gic.all_rename
#print axioms LeanProofs.ZFCinPA.R2Gic.ex_rename
#print axioms LeanProofs.ZFCinPA.R2Gic.ctx2_intro
#print axioms LeanProofs.ZFCinPA.R2Gic.encode_mem_bvars
#print axioms LeanProofs.ZFCinPA.R2Gic.enc_subst2
#print axioms LeanProofs.ZFCinPA.R2Gic.encode_gicBody
#print axioms LeanProofs.ZFCinPA.R2Gic.all_rename_ctx
#print axioms LeanProofs.ZFCinPA.R2Gic.ex_rename_ctx
#print axioms LeanProofs.ZFCinPA.R2Gic.mx_leibniz
#print axioms LeanProofs.ZFCinPA.R2Gic.gic_bridge_core

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {n : ℕ} (F B s : V) (φ : LeanProofs.ZFCinPA.R2Gic.SF (V := V) (n + 1)) :
    encode F B s (∀⁰ φ).val = wal s (encode F (s ∷ B) (s + 2) φ.val) :=
  LeanProofs.ZFCinPA.R2Gic.encT_all F B s φ
example {n : ℕ} (F B s : V) (φ : LeanProofs.ZFCinPA.R2Gic.SF (V := V) (n + 1)) :
    encode F B s (∃⁰ φ).val =
      wim (wal s (wim (encode F (s ∷ B) (s + 2) φ.val) 1)) 1 :=
  LeanProofs.ZFCinPA.R2Gic.encT_exs F B s φ
example {n : ℕ} (F B s : V) (φ ψ : LeanProofs.ZFCinPA.R2Gic.SF (V := V) n) :
    encode F B s (φ ⋏ ψ).val =
      wim (wim (encode F B s φ.val) (wim (encode F B s ψ.val) 1)) 1 :=
  LeanProofs.ZFCinPA.R2Gic.encT_and F B s φ ψ
example {n : ℕ} (F B s : V) (φ ψ : LeanProofs.ZFCinPA.R2Gic.SF (V := V) n) :
    encode F B s (φ ⋎ ψ).val =
      wim (wim (encode F B s φ.val) 1) (encode F B s ψ.val) :=
  LeanProofs.ZFCinPA.R2Gic.encT_or F B s φ ψ
example {n : ℕ} (F B s : V) (φ ψ : LeanProofs.ZFCinPA.R2Gic.SF (V := V) n) :
    encode F B s (φ 🡒 ψ).val =
      wim (wim (encode F B s (Bootstrapping.neg ℒₛₑₜ φ.val)) 1)
        (encode F B s ψ.val) :=
  LeanProofs.ZFCinPA.R2Gic.encT_imp F B s φ ψ

example {x y A B : V} (hL : CProv (wim (weq x y) (wim A B)))
    (vxB : Vac x B) (vy : Vac y (wal x A)) : CProv (wim (wal x A) (wal y B)) :=
  LeanProofs.ZFCinPA.R2Gic.all_rename hL vxB vy
example {x y A B : V} (hL : CProv (wim (weq x y) (wim A B)))
    (vyA : Vac y A) (vx : Vac x (ex y B)) : CProv (wim (ex x A) (ex y B)) :=
  LeanProofs.ZFCinPA.R2Gic.ex_rename hL vyA vx
example (u v u' v' : V) :
    CProv (wim (weq u u') (wim (weq v v')
      (eqContext (u ∷ v ∷ 0) (u' ∷ v' ∷ 0)))) :=
  LeanProofs.ZFCinPA.R2Gic.ctx2_intro u v u' v'

example {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (Bootstrapping.Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2)
      ![Bootstrapping.Semiterm.bvar i, Bootstrapping.Semiterm.bvar j]).val =
      wel B.[(i : V)] B.[(j : V)] :=
  LeanProofs.ZFCinPA.R2Gic.encode_mem_bvars F B s i j
example {n : ℕ} (F B s : V) (K : LeanProofs.ZFCinPA.R2Gic.SF (V := V) 2) (i j : Fin n) :
    encode F B s (K.subst ![Bootstrapping.Semiterm.bvar i, Bootstrapping.Semiterm.bvar j]).val =
      encode F (B.[(i : V)] ∷ B.[(j : V)] ∷ 0) s K.val :=
  LeanProofs.ZFCinPA.R2Gic.enc_subst2 F B s K i j
example (K : LeanProofs.ZFCinPA.R2Gic.SF (V := V) 2) (F t : V) :
    encode F 0 t (LeanProofs.ZFCinPA.gicBody K).val = wal t (ex (t + 2)
      (conj (LeanProofs.ZFCinPA.R2Gic.SUPc F t K.val)
        (LeanProofs.ZFCinPA.R2Gic.COVc F t K.val))) :=
  LeanProofs.ZFCinPA.R2Gic.encode_gicBody K F t

example {h x y A B : V} (hL : CProv (wim h (wim (weq x y) (wim A B))))
    (vxh : Vac x h) (vyh : Vac y h) (vxB : Vac x B) (vy : Vac y (wal x A)) :
    CProv (wim h (wim (wal x A) (wal y B))) :=
  LeanProofs.ZFCinPA.R2Gic.all_rename_ctx hL vxh vyh vxB vy
example {h x y A B : V} (hL : CProv (wim h (wim (weq x y) (wim A B))))
    (vxh : Vac x h) (vyh : Vac y h) (vyA : Vac y A) (vx : Vac x (ex y B)) :
    CProv (wim h (wim (ex x A) (ex y B))) :=
  LeanProofs.ZFCinPA.R2Gic.ex_rename_ctx hL vxh vyh vyA vx

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

example {K F w u v u' v' : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F)
    (hw : w % 2 = 1) (hFw : F < w) (h1w : 1 < w)
    (hu : u % 2 = 1) (hv : v % 2 = 1) (hu' : u' % 2 = 1) (hv' : v' % 2 = 1)
    (huw : u < w) (hvw : v < w) (hu'w : u' < w) (hv'w : v' < w) :
    CProv (wim (eqContext (u ∷ v ∷ 0) (u' ∷ v' ∷ 0))
      (wim (LeanProofs.ZFCinPA.R2Gic.Mx F w K u v)
        (LeanProofs.ZFCinPA.R2Gic.Mx F w K u' v'))) :=
  LeanProofs.ZFCinPA.R2Gic.mx_leibniz hK hF hw hFw h1w hu hv hu' hv' huw hvw hu'w hv'w
example (K : LeanProofs.ZFCinPA.R2Gic.SF (V := V) 2) {F a b t t2 t4 t6 t8 : V}
    (hF : OddEnv F) (oa : a % 2 = 1) (ob : b % 2 = 1) (ot : t % 2 = 1)
    (ot2 : t2 % 2 = 1) (ot4 : t4 % 2 = 1) (ot6 : t6 % 2 = 1) (ot8 : t8 % 2 = 1)
    (lFa : F < a) (l1a : 1 < a) (lab : a < b) (lbt : b < t) (ltt2 : t < t2)
    (lt24 : t2 < t4) (lt46 : t4 < t6) (lt68 : t6 < t8) :
    CProv (wal t (ex t2 (conj
      (LeanProofs.ZFCinPA.R2Gic.SUPg F t2 t4 t6 t8 K.val)
      (LeanProofs.ZFCinPA.R2Gic.COVg F t t2 t4 t6 t8 K.val)))) :=
  LeanProofs.ZFCinPA.R2Gic.gic_bridge_core K hF oa ob ot ot2 ot4 ot6 ot8
    lFa l1a lab lbt ltt2 lt24 lt46 lt68
