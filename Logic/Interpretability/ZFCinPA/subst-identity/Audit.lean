import ZFCinPA.SubstIdentity

set_option autoImplicit false

noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SubstIdentity

namespace LeanProofs.ZFCinPA.SubstIdentityTypedAudit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

example {m w : V} (hw : len w = m) (H : ∀ i < m, w.[i] = ^#i) :
    IsSemitermVec L m m w :=
  isSemitermVec_of_bvarVec hw H

example {m w p : V} (hp : IsSemiformula L m p)
    (hw : len w = m) (H : ∀ i < m, w.[i] = ^#i) :
    Bootstrapping.subst L w p = p :=
  subst_bvarVec_eq_self hp hw H

example {m n : ℕ} (φ : Bootstrapping.Semiformula V L m)
    (w : Bootstrapping.SemitermVec V L m n)
    (H : ∀ i : Fin m, (w i).val = ^#((i : ℕ) : V)) :
    (φ.subst w).val = φ.val :=
  SubstIdentity.Semiformula.subst_bvarVec_val φ w H

example {m n : ℕ} (h : m ≤ n) : Bootstrapping.SemitermVec V L m n :=
  SubstIdentity.Semiformula.bvarVec h

example {m n : ℕ} (h : m ≤ n) (i : Fin m) :
    ((SubstIdentity.Semiformula.bvarVec (V := V) (L := L) h) i).val =
      ^#((i : ℕ) : V) :=
  SubstIdentity.Semiformula.bvarVec_val h i

example {m n : ℕ} (h : m ≤ n) (φ : Bootstrapping.Semiformula V L m) :
    (φ.subst (SubstIdentity.Semiformula.bvarVec h)).val = φ.val :=
  SubstIdentity.Semiformula.subst_bvarVec h φ

example {m n : ℕ} (h : m ≤ n) (φ : Bootstrapping.Semiformula V L m) :
    Bootstrapping.Semiformula V L n :=
  SubstIdentity.Semiformula.castLE h φ

example {m n : ℕ} (h : m ≤ n) (φ : Bootstrapping.Semiformula V L m) :
    (SubstIdentity.Semiformula.castLE h φ).val = φ.val :=
  SubstIdentity.Semiformula.castLE_val h φ

example {m n : ℕ} (h : m ≤ n) (φ : Bootstrapping.Semiformula V L m) :
    φ.subst (SubstIdentity.Semiformula.bvarVec h) =
      SubstIdentity.Semiformula.castLE h φ :=
  SubstIdentity.Semiformula.subst_bvarVec_eq_castLE h φ

example {k : ℕ} {arities : Fin k → ℕ} {n : ℕ}
    (i : Fin k) (h : arities i ≤ n) :
    Fin (arities i) → ClosedSemiterm (setTemplateLanguage k arities) n :=
  srcBvars i h

example {k : ℕ} {arities : Fin k → ℕ} {n : ℕ}
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (i : Fin k) (h : arities i ≤ n) :
    (translateFormula Ks
      (Rewriting.emb (srcP i (srcBvars i h)) :
        Semiproposition (setTemplateLanguage k arities) n)).val = (Ks i).val :=
  translate_emb_srcP_bvars Ks i h

example {k : ℕ} {arities : Fin k → ℕ} {n : ℕ}
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (i : Fin k) (h : arities i ≤ n) :
    translateFormula Ks
      (Rewriting.emb (srcP i (srcBvars i h)) :
        Semiproposition (setTemplateLanguage k arities) n) =
      SubstIdentity.Semiformula.castLE h (Ks i) :=
  translate_emb_srcP_bvars_eq Ks i h

end LeanProofs.ZFCinPA.SubstIdentityTypedAudit

#print axioms LeanProofs.ZFCinPA.SubstIdentity.isSemitermVec_of_bvarVec
#print axioms LeanProofs.ZFCinPA.SubstIdentity.subst_bvarVec_eq_self
#print axioms LeanProofs.ZFCinPA.SubstIdentity.Semiformula.subst_bvarVec_val
#print axioms LeanProofs.ZFCinPA.SubstIdentity.Semiformula.bvarVec_val
#print axioms LeanProofs.ZFCinPA.SubstIdentity.Semiformula.subst_bvarVec
#print axioms LeanProofs.ZFCinPA.SubstIdentity.Semiformula.castLE_val
#print axioms LeanProofs.ZFCinPA.SubstIdentity.Semiformula.subst_bvarVec_eq_castLE
#print axioms LeanProofs.ZFCinPA.SubstIdentity.translate_emb_srcP_bvars
#print axioms LeanProofs.ZFCinPA.SubstIdentity.translate_emb_srcP_bvars_eq
