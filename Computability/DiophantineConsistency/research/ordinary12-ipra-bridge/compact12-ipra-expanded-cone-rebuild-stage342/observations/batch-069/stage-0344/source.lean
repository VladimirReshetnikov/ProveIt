import ZFCinPA.ValidatorNativeGic254

set_option autoImplicit false
noncomputable section

/-!
Finite matrix congruence for the literal validator GIC circuit. All codes and
labels are arbitrary values of an internal arithmetic model. The circuit's
three labels stay fixed throughout; no freshness or renaming premise is used.
Padding is removed from the matrix while its witness label remains `pad p`.
This does not identify a configurable Foundation encoding or prove alpha
transport, arbitrary universal closure, or an internal consistency endpoint.
-/
namespace LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open ValidatorProvability254 ValidatorQuantifierCore254 ValidatorNativeGic254
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

/-- Implication is contravariant in its antecedent and covariant in its consequent. -/
lemma cProv_imp_mono {p p' q q' : V}
    (hp : CProv (wim p' p)) (hq : CProv (wim q q')) :
    CProv (wim (wim p q) (wim p' q')) :=
  ded2 (.mp (.ax hq) (.mp h1 (.mp (.ax hp) h0)))

lemma cProv_conj_mono {p p' q q' : V}
    (hp : CProv (wim p p')) (hq : CProv (wim q q')) :
    CProv (wim (conj p q) (conj p' q')) :=
  contrapose_of (cProv_imp_mono hp (contrapose_of hq))

/-- Both matrix directions are needed because the matrix occurs in both polarities. -/
lemma internalGic_matrix_imp (a b c : V) {p q : V}
    (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (internalGic a b c p) (internalGic a b c q)) := by
  have hpair : CProv (wim (conj p (wel b c)) (conj q (wel b c))) :=
    cProv_conj_mono hpq (Kalmar.self_imp cProv_classical (wel b c))
  have hmatrix : CProv
      (wim (wim p (ex b (conj p (wel b c))))
        (wim q (ex b (conj q (wel b c))))) :=
    cProv_imp_mono hqp (ex_mono b hpair)
  have hleft : CProv
      (wim (wal a (wim (wel a b) (wal b (wim p (ex b (conj p (wel b c)))))))
        (wal a (wim (wel a b) (wal b (wim q (ex b (conj q (wel b c)))))))) :=
    all_mono a (cProv_imp_mono (Kalmar.self_imp cProv_classical (wel a b))
      (all_mono b hmatrix))
  have hright : CProv
      (wim (wal b (wim (wel b c) (ex a p)))
        (wal b (wim (wel b c) (ex a q)))) :=
    all_mono b (cProv_imp_mono (Kalmar.self_imp cProv_classical (wel b c))
      (ex_mono a hpq))
  exact ex_mono c (cProv_conj_mono hleft hright)

lemma internalGic_matrix_equivalent (a b c : V) {p q : V}
    (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (internalGic a b c p) (internalGic a b c q)) ∧
      CProv (wim (internalGic a b c q) (internalGic a b c p)) :=
  ⟨internalGic_matrix_imp a b c hpq hqp, internalGic_matrix_imp a b c hqp hpq⟩

/-- The existential witness label is the same `pad p` on both sides. -/
lemma internalGic_pad_equivalent (a b p : V) :
    CProv (wim (internalGic a b (pad p) p) (internalGic a b (pad p) (pad p))) ∧
      CProv (wim (internalGic a b (pad p) (pad p)) (internalGic a b (pad p) p)) :=
  internalGic_matrix_equivalent a b (pad p) (pad_equivalent p).1 (pad_equivalent p).2

lemma cProv_unpaddedGic_bounded (a b p : V) (ha : a ≤ 3) (hb : b ≤ 3) :
    CProv (internalGic a b (pad p) p) :=
  cProv_mp (internalGic_pad_equivalent a b p).2 (cProv_paddedGic_bounded a b p ha hb)

theorem cProv_unpaddedGic (p : V) : CProv (internalGic 1 3 (pad p) p) :=
  cProv_mp (internalGic_pad_equivalent 1 3 p).2 (cProv_paddedGic p)

/-- Generalize the domain label only, retaining the literal circuit and witness label. -/
theorem cProv_closed_unpaddedGic (p : V) :
    CProv (wal 3 (internalGic 1 3 (pad p) p)) :=
  cProv_gen 3 (cProv_unpaddedGic p)

end LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254
