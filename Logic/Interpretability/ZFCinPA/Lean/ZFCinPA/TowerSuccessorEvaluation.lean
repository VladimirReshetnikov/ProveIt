import ZFCinPA.TowerEvaluation

/-!
# The evaluation bridge, part two (c): the level tower one index up

The successor forms of `ZFCinPA.TowerEvaluation`'s four readings.  They are
where the nineteen-leaf closure-step spine of `ZFCinPA.SuccessorSources` is
consumed: `srcLevelSatSuccAt` splices the two successor spines
(`srcNumChainSucc`, `srcClosStep`) into the unfolded-instance shape, so its
reading is `EnlargedFields.Step` over the placeholder level at a bound the
numeral placeholder supplies — that is `templateStepLevel`.

**The bound is existentially quantified.**  `templateStepLevel` says
"*some* numeral witness `k` satisfies `Num`, and the record is certified at
bound `k⁺`"; the numeral placeholder is opaque, so nothing at this level
forces two occurrences to pick the same `k`.  That is a genuine obligation
of the assembled source sentence, recorded here rather than discovered
later; see the residue section of `ZFCinPA.FieldEvaluation`.
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

section TowerSucc

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The canonical level instance one index up** is the closure level over
the placeholder level, at a successor bound. -/
theorem eval_srcLevelSatSuccAt (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcLevelSatSuccAt m) ↔
      templateStepLevel X H (e 2) (e 1) (e 0) := by
  refine Iff.trans (eval_srcLvlInst m (fTripleMemF 4 3 2 1)
    (srcNumChainSucc (m + 1 + 1)) (srcClosStep (m + 1 + 1)) h
    (fun _ n ↦ ∃ k, templateNum X k ∧ n = vsucc H k)
    (fun C n ↦ LevelClosed H (templateLevel X H) n C)
    (fun C n ↦ eval_srcNumChainSucc (m + 1 + 1) ((h.cons C).cons n) H)
    (fun C n ↦ eval_srcClosStep (m + 1 + 1) ((h.cons C).cons n) H)) ?_
  constructor
  · rintro ⟨C, n, ⟨k, hk, rfl⟩, hcl, hm⟩
    exact ⟨k, hk, C, hcl,
      (fTripleMemF_spec H (scons (vsucc H k) (scons C e)) 4 3 2 1).mp hm⟩
  · rintro ⟨k, hk, C, hcl, hm⟩
    exact ⟨C, vsucc H k, ⟨k, hk, rfl⟩, hcl,
      (fTripleMemF_spec H (scons (vsucc H k) (scons C e)) 4 3 2 1).mpr hm⟩

/-- The bit-`w` witness wrapper one index up. -/
theorem eval_srcBitWitnessSuccAt (m w : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcBitWitnessSuccAt m w) ↔
      templateStepLevel X H (e 1) (e 0) (natV H w) := by
  rw [srcBitWitnessSuccAt, Semiformula.eval_ex]
  constructor
  · rintro ⟨y, hy⟩
    rw [LogicalConnective.HomClass.map_and] at hy
    have hy1 : y = natV H w :=
      (fNumF_spec H w 0 (scons y e)).mp
        ((eval_liftP (h.cons y) (fNumF 0 w)).mp hy.1)
    have hy2 : templateStepLevel X H (e 1) (e 0) y :=
      (eval_srcLevelSatSuccAt (m + 1) (h.cons y) H).mp hy.2
    rwa [hy1] at hy2
  · intro hh
    refine ⟨natV H w, ?_⟩
    rw [LogicalConnective.HomClass.map_and]
    exact ⟨(eval_liftP (h.cons (natV H w)) (fNumF 0 w)).mpr
        ((fNumF_spec H w 0 (scons (natV H w) e)).mpr rfl),
      (eval_srcLevelSatSuccAt (m + 1) (h.cons (natV H w)) H).mpr hh⟩

/-- The polarized gadget one index up. -/
theorem eval_srcPolarAtSucc (m w ci ei : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcPolarAtSucc m w ci ei) ↔
      templateStepLevel X H (e ci) (e ei) (natV H w) := by
  rw [srcPolarAtSucc]
  exact eval_srcCanonAtPair m ci ei _ h
    (fun x1 x0 ↦ templateStepLevel X H x1 x0 (natV H w))
    (fun x1 x0 ↦
      eval_srcBitWitnessSuccAt (m + 1 + 1) w ((h.cons x1).cons x0) H)

end TowerSucc

end TemplateEvaluation
end ZFCinPA
end LeanProofs
