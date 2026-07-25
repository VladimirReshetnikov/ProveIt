import ZFCinPA.SpineEvaluation

/-!
# The evaluation bridge, part two (b): the level tower

With the closure spine read (`ZFCinPA.SpineEvaluation`), the level tower at
the canonical slots follows.  Two levels are involved:

* the **placeholder level** `TemplateEvaluation.templateLevel`, the source
  spine's reading of the two opaque relations, and
* the level one index up, which is `EnlargedFields.Step` over it at a bound
  the numeral placeholder supplies — `templateStepLevel`.

The four readings this module lands are the ones the certificate fields
consume: the canonical level instance (`eval_srcLevelSatAt`), the bit-`w`
witness wrapper (`eval_srcBitWitnessAt`), the canonical-slot gadget
(`eval_srcCanonAtPair`) and their composite, the polarized gadget
(`eval_srcPolarAt`), which is the source counterpart of
`CertificateFields.polarAtCode`.  Their successor forms are in
`ZFCinPA.TowerSuccessorEvaluation`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace LeanProofs
namespace ZFCinPA
namespace TemplateEvaluation

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open BoundedZFCConsistency
open SetTheory (Form ZFAxioms scons Sat vsucc)

section Tower

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The successor level induced by the source spine.**  The numeral
placeholder supplies a witness `k`, and the level one index up is the
closure level over `templateLevel` at the bound `k⁺` — which is exactly the
shape `EnlargedFields.exclusivity_step` and
`LocalStepTransfer.localStepLaws_step` are stated at. -/
def templateStepLevel (X : Type*) [Structure srcL X]
    (H : ZFAxioms (templateMem X)) (c en bi : X) : Prop :=
  ∃ k, templateNum X k ∧
    EnlargedFields.Step H (templateLevel X H) (vsucc H k) c en bi

/-- The canonical level instance, at an arbitrary ambient arity. -/
theorem eval_srcLevelSatAt (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcLevelSatAt m) ↔
      templateLevel X H (e 2) (e 1) (e 0) :=
  eval_srcLvlInstP_triple m 2 1 0 h H

/-- **The numeral-chain successor spine.**  The next index is the successor
of some index the placeholder recognizes. -/
theorem eval_srcNumChainSucc (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcNumChainSucc m) ↔
      ∃ k, templateNum X k ∧ e 0 = vsucc H k := by
  rw [srcNumChainSucc, Semiformula.eval_ex]
  refine exists_congr fun k ↦ ?_
  rw [LogicalConnective.HomClass.map_and, eval_srcNumAt,
    eval_liftP (h.cons k) (SetTheory.fSuccF 1 0),
    SetTheory.fSuccF_spec H (scons k e) 1 0]
  exact Iff.rfl

/-- **The bit-`w` witness wrapper**: the level relation at the numeral
bit. -/
theorem eval_srcBitWitnessAt (m w : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcBitWitnessAt m w) ↔
      templateLevel X H (e 1) (e 0) (natV H w) := by
  rw [srcBitWitnessAt, Semiformula.eval_ex]
  constructor
  · rintro ⟨y, hy⟩
    rw [LogicalConnective.HomClass.map_and] at hy
    have hy1 : y = natV H w :=
      (fNumF_spec H w 0 (scons y e)).mp
        ((eval_liftP (h.cons y) (fNumF 0 w)).mp hy.1)
    have hy2 : templateLevel X H (e 1) (e 0) y :=
      (eval_srcLevelSatAt (m + 1) (h.cons y) H).mp hy.2
    rwa [hy1] at hy2
  · intro hh
    refine ⟨natV H w, ?_⟩
    rw [LogicalConnective.HomClass.map_and]
    exact ⟨(eval_liftP (h.cons (natV H w)) (fNumF 0 w)).mpr
        ((fNumF_spec H w 0 (scons (natV H w) e)).mpr rfl),
      (eval_srcLevelSatAt (m + 1) (h.cons (natV H w)) H).mpr hh⟩

/-- **The canonical-slot gadget selects the two named slots.**  The two
equality guards force the bound variables, so the reading is the payload at
the slot pair. -/
theorem eval_srcCanonAtPair (m ci ei : ℕ)
    (inner : Semiproposition srcL (m + 1 + 1)) {b : Fin m → X}
    {f e : ℕ → X} (h : Corr b f e) (P : X → X → Prop)
    (hi : ∀ x1 x0 : X,
      Semiformula.Eval (s := sX) (x0 :> x1 :> b) f inner ↔ P x1 x0) :
    Semiformula.Eval (s := sX) b f (srcCanonAtPair m ci ei inner) ↔
      P (e ci) (e ei) := by
  rw [srcCanonAtPair]
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply]
  constructor
  · intro hh
    refine (hi (e ci) (e ei)).mp (hh (e ci) (e ei) ?_ ?_)
    · exact (eval_liftP ((h.cons (e ci)).cons (e ei))
        (Form.fEq 1 (ci + 2))).mpr rfl
    · exact (eval_liftP ((h.cons (e ci)).cons (e ei))
        (Form.fEq 0 (ei + 2))).mpr rfl
  · intro hh x1 x0 k1 k2
    have k1' : x1 = e ci :=
      (eval_liftP ((h.cons x1).cons x0) (Form.fEq 1 (ci + 2))).mp k1
    have k2' : x0 = e ei :=
      (eval_liftP ((h.cons x1).cons x0) (Form.fEq 0 (ei + 2))).mp k2
    subst k1'
    subst k2'
    exact (hi _ _).mpr hh

/-- **The polarized gadget** — the source counterpart of
`CertificateFields.polarAtCode` — reads the level relation at the two named
slots and the numeral bit. -/
theorem eval_srcPolarAt (m w ci ei : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcPolarAt m w ci ei) ↔
      templateLevel X H (e ci) (e ei) (natV H w) := by
  rw [srcPolarAt]
  exact eval_srcCanonAtPair m ci ei _ h
    (fun x1 x0 ↦ templateLevel X H x1 x0 (natV H w))
    (fun x1 x0 ↦ eval_srcBitWitnessAt (m + 1 + 1) w ((h.cons x1).cons x0) H)

end Tower

end TemplateEvaluation
end ZFCinPA
end LeanProofs
