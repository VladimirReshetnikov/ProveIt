import ZFCinPA.R2Fixed

namespace LeanProofs.ZFCinPA.R2FixedFreshAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Gic
open scoped LO.FirstOrder.Arithmetic
set_option autoImplicit false

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

#print axioms LeanProofs.ZFCinPA.R2Fixed.encode_eq_bvars
#print axioms LeanProofs.ZFCinPA.R2Fixed.encode_nrelT
#print axioms LeanProofs.ZFCinPA.R2Fixed.encode_neqA
#print axioms LeanProofs.ZFCinPA.R2Fixed.encode_nmemA
#print axioms LeanProofs.ZFCinPA.R2Fixed.refl_ax
#print axioms LeanProofs.ZFCinPA.R2Fixed.symm_ax
#print axioms LeanProofs.ZFCinPA.R2Fixed.trans_ax
#print axioms LeanProofs.ZFCinPA.R2Fixed.relExt_mem_ax
#print axioms LeanProofs.ZFCinPA.R2Fixed.relExt_eq_ax
#print axioms LeanProofs.ZFCinPA.R2Fixed.wel_zero_zero
#print axioms LeanProofs.ZFCinPA.R2Fixed.not_mem_self
#print axioms LeanProofs.ZFCinPA.R2Fixed.irr_ax
#print axioms LeanProofs.ZFCinPA.R2Fixed.negEx_all
#print axioms LeanProofs.ZFCinPA.R2Fixed.container_core
#print axioms LeanProofs.ZFCinPA.R2Fixed.encode_containerAx
#print axioms LeanProofs.ZFCinPA.R2Fixed.container_ax

example {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (LeanProofs.ZFCinPA.R2Fixed.eqA (V := V) i j).val =
      weq B.[(i : V)] B.[(j : V)] :=
  LeanProofs.ZFCinPA.R2Fixed.encode_eq_bvars F B s i j

example {k n : ℕ} (F B s : V) (R : (ℒₛₑₜ).Rel k)
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k n) :
    encode F B s (Bootstrapping.Semiformula.nrel R v).val =
      wim (encode F B s (Bootstrapping.Semiformula.rel R v).val) 1 :=
  LeanProofs.ZFCinPA.R2Fixed.encode_nrelT F B s R v

example {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (LeanProofs.ZFCinPA.R2Fixed.neqA (V := V) i j).val =
      wim (weq B.[(i : V)] B.[(j : V)]) 1 :=
  LeanProofs.ZFCinPA.R2Fixed.encode_neqA F B s i j

example {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (LeanProofs.ZFCinPA.R2Fixed.nmemA (V := V) i j).val =
      wim (wel B.[(i : V)] B.[(j : V)]) 1 :=
  LeanProofs.ZFCinPA.R2Fixed.encode_nmemA F B s i j

example (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.refl_ax F s

example (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.symm_ax F s

example (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.trans_ax F s

example (F s : V) :
    CProv (encode F 0 s
      (⌜(Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.relExt_mem_ax F s

example (F s : V) :
    CProv (encode F 0 s
      (⌜(Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.relExt_eq_ax F s

example : wel (0 : V) 0 = 1 :=
  LeanProofs.ZFCinPA.R2Fixed.wel_zero_zero

example (s : V) : CProv (wim (wel s s) 1) :=
  LeanProofs.ZFCinPA.R2Fixed.not_mem_self s

example (F s : V) : CProv (encode F 0 s (⌜NativeSet.irAx⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.irr_ax F s

example (W Z Y : V) :
    CProv (wim (neg (ex W (conj (wel W Z) (neg (wel W Y)))))
      (wal W (wim (wel W Z) (wel W Y)))) :=
  LeanProofs.ZFCinPA.R2Fixed.negEx_all W Z Y

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

example {a b c X C Y P Z W : V}
    (lab : a < b) (lbc : b < c) (lcX : c < X) (lXC : X < C)
    (lCY : C < Y) (lYP : Y < P) (lPZ : P < Z) (lZW : Z < W) :
    CProv (wal X (ex C (conj (wel X C) (wal Y (wim (neg (neg (wel Y C)))
      (conj (wal P (wim (neg (neg (wel P Y))) (wel P C)))
        (ex P (conj (wel P C) (wal Z (wim (neg (ex W (conj (wel W Z) (neg (wel W Y)))))
          (wel Z P))))))))))) :=
  LeanProofs.ZFCinPA.R2Fixed.container_core lab lbc lcX lXC lCY lYP lPZ lZW

example (F t : V) :
    encode F 0 t (⌜NativeSet.containerAx⌝ : V) =
      wal t (ex (t + 2) (conj (wel t (t + 2)) (wal (t + 2 + 2)
        (wim (neg (neg (wel (t + 2 + 2) (t + 2))))
          (conj (wal (t + 2 + 2 + 2)
            (wim (neg (neg (wel (t + 2 + 2 + 2) (t + 2 + 2))))
              (wel (t + 2 + 2 + 2) (t + 2))))
            (ex (t + 2 + 2 + 2) (conj (wel (t + 2 + 2 + 2) (t + 2))
              (wal (t + 2 + 2 + 2 + 2)
                (wim (neg (ex (t + 2 + 2 + 2 + 2 + 2)
                  (conj (wel (t + 2 + 2 + 2 + 2 + 2) (t + 2 + 2 + 2 + 2))
                    (neg (wel (t + 2 + 2 + 2 + 2 + 2) (t + 2 + 2))))))
                  (wel (t + 2 + 2 + 2 + 2) (t + 2 + 2 + 2))))))))))) :=
  LeanProofs.ZFCinPA.R2Fixed.encode_containerAx F t

example {F s : V} (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (encode F 0 s (⌜NativeSet.containerAx⌝ : V)) :=
  LeanProofs.ZFCinPA.R2Fixed.container_ax hF hs

end LeanProofs.ZFCinPA.R2FixedFreshAudit
