import BusyBeaver.ZFC.ConstructibleDef

/-!
Gödel's constructible hierarchy inside a model of ZF.

`IsL a S` says that `S = L_a`: the stage `a` of the hierarchy of
`ConstructibleDef.Gdef` (`TransRec`). This module proves the basic facts:

* the **truth bridge** `satIn_formCode`: for a standard formula `φ`, internal
  satisfaction of its code over `(X, ∈)` is satisfaction of `φ` with
  quantifiers bounded by `X` (`RSat`), read at the environment's values;
* every member of a transitive set `X` is definable over `X`, and so is `X`
  itself, so stages are transitive, increasing, and `L_a ∈ L_{a+1}`.
-/

namespace SetTheory.BusyBeaver.ZFC.Constructible

open NamedZF NForm InternalOrd InternalRank TransRec ConstructibleDef
  LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ## Satisfaction with bounded quantifiers -/

/-- Satisfaction with every quantifier bounded by `X`. -/
def RSat (mem : V → V → Prop) (X : V) : (Nat → V) → Form → Prop
  | e, .fMem i j => mem (e i) (e j)
  | e, .fEq i j => e i = e j
  | _, .fBot => False
  | e, .fImp a b => RSat mem X e a → RSat mem X e b
  | e, .fAnd a b => RSat mem X e a ∧ RSat mem X e b
  | e, .fOr a b => RSat mem X e a ∨ RSat mem X e b
  | e, .fAll a => ∀ d, mem d X → RSat mem X (scons d e) a
  | e, .fEx a => ∃ d, mem d X ∧ RSat mem X (scons d e) a

theorem rsat_congr (X : V) (φ : Form) {e e' : Nat → V} (h : ∀ n, e n = e' n) :
    RSat mem X e φ ↔ RSat mem X e' φ := by
  have : e = e' := funext h
  subst this; exact Iff.rfl

/-- The values of an internal environment, as an external one. -/
noncomputable def envVals (H : ZFAxioms mem) (e : V) : Nat → V := fun n => applyV H e (natV H n)

theorem envVals_econs (H : ZFAxioms mem) {X e : V} (he : IsEnvOn H X e) (d : V) (n : Nat) :
    envVals H (econs H d e) n = scons d (envVals H e) n := by
  cases n with
  | zero => exact econs_zero H he.1.1 d
  | succ n => exact econs_succ H he d (natV_mem_omega H n)

theorem setStructure_of_memRel (H : ZFAxioms mem) {X R : V} (hR : MemRel H X R)
    (hne : ∃ d, mem d X) : IsSetStructure H X R :=
  ⟨hne, fun p hp => by obtain ⟨a, b, ha, hb, -, rfl⟩ := (hR p).1 hp; exact ⟨a, b, ha, hb, rfl⟩⟩

/-- **The truth bridge.** Internal satisfaction of a standard formula's code
is satisfaction with quantifiers bounded by the carrier. -/
theorem satIn_formCode (H : ZFAxioms mem) {X R : V} (hS : IsSetStructure H X R)
    (hR : MemRel H X R) :
    ∀ (φ : Form) (e : V), IsEnvOn H X e →
      (SatIn H X R (formCode H φ) e ↔ RSat mem X (envVals H e) φ)
  | .fMem i j, e, he => by
      rw [formCode_fMem, satIn_memAtom H hS (natV_mem_omega H i) (natV_mem_omega H j) he, hR]
      constructor
      · rintro ⟨a, b, -, -, hab, hp⟩
        obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ hp
        exact hab
      · intro h
        exact ⟨_, _, isEnvOn_apply H he (natV_mem_omega H i), isEnvOn_apply H he (natV_mem_omega H j),
          h, rfl⟩
  | .fEq i j, e, he => by
      rw [formCode_fEq, satIn_eqAtom H hS (natV_mem_omega H i) (natV_mem_omega H j) he]
      rfl
  | .fBot, e, he => by
      rw [formCode_fBot]
      exact ⟨fun h => satIn_bot H h, False.elim⟩
  | .fImp a b, e, he => by
      rw [formCode_fImp, satIn_imp H hS (formCode_isFormCodeSem H a) (formCode_isFormCodeSem H b) he,
        satIn_formCode H hS hR a e he, satIn_formCode H hS hR b e he]
      rfl
  | .fAnd a b, e, he => by
      rw [formCode_fAnd, satIn_and H hS (formCode_isFormCodeSem H a) (formCode_isFormCodeSem H b) he,
        satIn_formCode H hS hR a e he, satIn_formCode H hS hR b e he]
      rfl
  | .fOr a b, e, he => by
      rw [formCode_fOr, satIn_or H hS (formCode_isFormCodeSem H a) (formCode_isFormCodeSem H b) he,
        satIn_formCode H hS hR a e he, satIn_formCode H hS hR b e he]
      rfl
  | .fAll a, e, he => by
      rw [formCode_fAll, satIn_all H hS (formCode_isFormCodeSem H a) he]
      refine forall_congr' fun d => imp_congr_right fun hd => ?_
      rw [satIn_formCode H hS hR a _ (econs_isEnvOn H he hd)]
      exact rsat_congr X a (envVals_econs H he d)
  | .fEx a, e, he => by
      rw [formCode_fEx, satIn_ex H hS (formCode_isFormCodeSem H a) he]
      refine exists_congr fun d => and_congr_right fun hd => ?_
      rw [satIn_formCode H hS hR a _ (econs_isEnvOn H he hd)]
      exact rsat_congr X a (envVals_econs H he d)

/-! ## Definable members -/

section Members

variable (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hP

omit hP in
theorem constEnv_apply {d n : V} (hn : mem n (omegaV H)) : applyV H (constEnv H d) n = d := by
  obtain ⟨y, hy⟩ := (constEnv_isEnvOn H (A := vsingle H d) ((vsingle_spec H d d).2 rfl)).1.2.1 n hn
  have h1 := applyV_eq H (constEnv_isEnvOn H (A := vsingle H d) ((vsingle_spec H d d).2 rfl)).1.1 hy
  have h2 := (constEnv_isEnvOn H (A := vsingle H d) ((vsingle_spec H d d).2 rfl)).2 n y hy
  rw [h1]; exact (vsingle_spec H d y).1 h2

/-- A set definable over `X` by a standard formula with one parameter. -/
theorem definable_formCode {X a : V} (ha : mem a X) (φ : Form) (S : V)
    (hS : ∀ y, mem y S ↔ mem y X ∧ RSat mem X (scons y (fun _ => a)) φ) : DefinableIn H X S := by
  obtain ⟨R, hR⟩ := memRel_exists H hP X
  have hst := setStructure_of_memRel H hR ⟨a, ha⟩
  have he := constEnv_isEnvOn H (A := X) ha
  refine ⟨R, formCode H φ, constEnv H a, hR, formCode_isFormCodeSem H φ, he, fun y => ?_⟩
  rw [hS y]
  refine and_congr_right fun hy => ?_
  rw [satIn_formCode H hst hR φ _ (econs_isEnvOn H he hy)]
  refine rsat_congr X φ fun n => ?_
  rw [envVals_econs H he y n]
  cases n with
  | zero => rfl
  | succ n => exact (constEnv_apply H (natV_mem_omega H n)).symm

/-- Every member of a transitive set is definable over it. -/
theorem mem_gdef_of_mem {X a : V} (hX : Trans mem X) (ha : mem a X) : mem a (Gdef H hP X) := by
  refine (gdef_spec H hP X a).2 ⟨fun z hz => hX a ha z hz, Or.inr ?_⟩
  exact definable_formCode H hP ha (.fMem 0 1) a fun y =>
    ⟨fun hy => ⟨hX a ha y hy, hy⟩, fun h => h.2⟩

/-- Every set is definable over itself. -/
theorem self_mem_gdef (X : V) : mem X (Gdef H hP X) := by
  refine (gdef_spec H hP X X).2 ⟨fun _ h => h, ?_⟩
  by_cases hne : ∃ d, mem d X
  · obtain ⟨d, hd⟩ := hne
    exact Or.inr (definable_formCode H hP hd (.fEq 0 0) X fun y => ⟨fun hy => ⟨hy, rfl⟩, fun h => h.1⟩)
  · exact Or.inl fun z hz => hne ⟨z, hz⟩

end Members

/-! ## The constructible stages -/

section Stages

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- `S = L_a`. -/
def IsL (a S : V) : Prop := IsStage H (Gdef H hP) a S

theorem isL_exists {a : V} (ha : Ord mem a) : ∃ S, IsL H hP a S :=
  stage_exists' H hR (defOp H hP) ha

theorem isL_unique {a S S' : V} (ha : Ord mem a) (h : IsL H hP a S) (h' : IsL H hP a S') : S = S' :=
  stage_unique H hR ha h h'

theorem isL_spec {a S : V} (ha : Ord mem a) (h : IsL H hP a S) :
    ∀ z, mem z S ↔ ∃ c T, mem c a ∧ IsL H hP c T ∧ mem z (Gdef H hP T) :=
  stage_spec H hR (defOp H hP) ha h

theorem isL_mono {a c S T : V} (ha : Ord mem a) (hc : mem c a) (hT : IsL H hP c T)
    (hS : IsL H hP a S) : Sub mem T S :=
  stage_mono H hR (defOp H hP) ha hc hT hS

/-- Stages are transitive. -/
theorem isL_trans {a S : V} (ha : Ord mem a) (hS : IsL H hP a S) : Trans mem S := by
  intro z hz w hw
  obtain ⟨c, T, hc, hT, hzT⟩ := (isL_spec H hR hP ha hS z).1 hz
  exact isL_mono H hR hP ha hc hT hS w (((gdef_spec H hP T z).1 hzT).1 w hw)

/-- `L_c ⊆ G(L_c) ⊆ L_a` for `c ∈ a`: each stage is a member of the next. -/
theorem isL_mem {a c S T : V} (ha : Ord mem a) (hc : mem c a) (hT : IsL H hP c T)
    (hS : IsL H hP a S) : mem T S :=
  (isL_spec H hR hP ha hS T).2 ⟨c, T, hc, hT, self_mem_gdef H hP T⟩

end Stages

end SetTheory.BusyBeaver.ZFC.Constructible
