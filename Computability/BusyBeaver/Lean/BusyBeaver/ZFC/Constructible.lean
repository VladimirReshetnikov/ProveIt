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
    RSat mem X e φ ↔ RSat mem X e' φ := by rw [funext h]

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
      refine ⟨fun ⟨a, b, _, _, hab, hp⟩ => ?_, fun h => ⟨_, _,
        isEnvOn_apply H he (natV_mem_omega H i), isEnvOn_apply H he (natV_mem_omega H j), h, rfl⟩⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ hp
      exact hab
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
  have he := constEnv_isEnvOn H (A := vsingle H d) ((vsingle_spec H d d).2 rfl)
  obtain ⟨y, hy⟩ := he.1.2.1 n hn
  rw [applyV_eq H he.1.1 hy]; exact (vsingle_spec H d y).1 (he.2 n y hy)

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

/-! ## Definability with several parameters -/

section Params

variable (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hP

/-- A set cut out of `X` by a standard formula, with parameters read from an
internal environment over `X`, is definable over `X`. -/
theorem definable_env {X e : V} (he : IsEnvOn H X e) (φ : Form) (S : V)
    (hS : ∀ y, mem y S ↔ mem y X ∧ RSat mem X (scons y (envVals H e)) φ) : DefinableIn H X S := by
  obtain ⟨R, hR⟩ := memRel_exists H hP X
  have hne : ∃ d, mem d X := ⟨_, isEnvOn_apply H he (vempty_in_omega H)⟩
  have hst := setStructure_of_memRel H hR hne
  refine ⟨R, formCode H φ, e, hR, formCode_isFormCodeSem H φ, he, fun y => ?_⟩
  rw [hS y]
  refine and_congr_right fun hy => ?_
  rw [satIn_formCode H hst hR φ _ (econs_isEnvOn H he hy)]
  exact rsat_congr X φ fun n => (envVals_econs H he y n).symm

end Params

/-! ## Ordinals in L -/

/-- `x₀` is an ordinal: transitive, with transitive members. -/
def ordForm : Form :=
  .fAnd (.fAll (.fImp (.fMem 0 1) (.fAll (.fImp (.fMem 0 1) (.fMem 0 2)))))
    (.fAll (.fImp (.fMem 0 1) (.fAll (.fImp (.fMem 0 1) (.fAll (.fImp (.fMem 0 1) (.fMem 0 2)))))))

/-- Being an ordinal is absolute for transitive sets. -/
theorem rsat_ordForm {X x : V} (hX : Trans mem X) (hx : mem x X) (e : Nat → V) :
    RSat mem X (scons x e) ordForm ↔ Ord mem x := by
  simp only [ordForm, RSat, scons]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy z hz => h1 y (hX x hx y hy) hy z (hX y (hX x hx y hy) z hz) hz,
      fun y hy z hz w hw => ?_⟩
    have hyX := hX x hx y hy
    have hzX := hX y hyX z hz
    exact h2 y hyX hy z hzX hz w (hX z hzX w hw) hw
  · rintro ⟨h1, h2⟩
    exact ⟨fun y _ hy z _ hz => h1 y hy z hz, fun y _ hy z _ hz w _ hw => h2 y hy z hz w hw⟩

section OrdinalsInL

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- **`L_a ∩ Ord = a`.** -/
theorem isL_ord : ∀ a, Ord mem a → ∀ S, IsL H hP a S → ∀ x, (mem x S ∧ Ord mem x) ↔ mem x a := by
  refine ord_induction H hR _
    (.all 1 (.imp (isStageF (defOp H hP) 0 1) (.all 2 ((NForm.and (.mem 2 1) (ordF 2)).iff (.mem 2 0)))))
    (fun _ => vempty H)
    (fun a => by
      simp only [NSat, nsat_isStageF H (defOp H hP), nsat_ordF, nsat_iff]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) ?_
  intro a ha IH S hS x
  constructor
  · rintro ⟨hxS, hx⟩
    obtain ⟨c, T, hc, hT, hxT⟩ := (isL_spec H hR hP ha hS x).1 hxS
    have hsub : Sub mem x T := ((gdef_spec H hP T x).1 hxT).1
    have hle := le_of_sub H hR hx (ord_of_mem ha hc) fun y hy =>
      (IH c hc T hT y).1 ⟨hsub y hy, ord_of_mem hx hy⟩
    exact hle.elim (fun e => e ▸ hc) fun h => ha.1 c hc x h
  · intro hxa
    have hx := ord_of_mem ha hxa
    obtain ⟨T, hT⟩ := isL_exists H hR hP hx
    refine ⟨(isL_spec H hR hP ha hS x).2 ⟨x, T, hxa, hT, ?_⟩, hx⟩
    have hTt := isL_trans H hR hP hx hT
    refine (gdef_spec H hP T x).2 ⟨fun y hy => ((IH x hxa T hT y).2 hy).1, ?_⟩
    by_cases hne : ∃ d, mem d T
    · obtain ⟨d, hd⟩ := hne
      exact Or.inr (definable_env H hP (constEnv_isEnvOn H (A := T) hd) ordForm x fun y =>
        ⟨fun hy => ((IH x hxa T hT y).2 hy).elim fun hyT hyo =>
          ⟨hyT, (rsat_ordForm hTt hyT _).2 hyo⟩,
          fun ⟨hyT, hy⟩ => (IH x hxa T hT y).1 ⟨hyT, (rsat_ordForm hTt hyT _).1 hy⟩⟩)
    · exact Or.inl fun z hz => hne ⟨z, ((IH x hxa T hT z).2 hz).1⟩

/-- Every ordinal is constructible: `a ∈ L_{a+1}`. -/
theorem ord_mem_isL {a S : V} (ha : Ord mem a) (hS : IsL H hP (vsucc H a) S) : mem a S :=
  ((isL_ord H hR hP _ (ord_succ H ha) S hS a).2 (vsucc_self H a)).1

end OrdinalsInL

/-! ## The constructible class -/

/-- `x` is constructible. -/
def InL (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (x : V) : Prop :=
  ∃ a S, Ord mem a ∧ IsL H hP a S ∧ mem x S

/-- The named formula for `InL` (free name `x`). -/
noncomputable def inLF (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (x : Nat) :
    NForm :=
  .ex (x + 1) (.ex (x + 2) (.and (ordF (x + 1)) (.and (isStageF (defOp H hP) (x + 1) (x + 2))
    (.mem x (x + 2)))))

theorem nsat_inLF (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (ρ : Nat → V)
    (x : Nat) : NSat mem ρ (inLF H hP x) ↔ InL H hP (ρ x) := by
  simp only [inLF, NSat, nsat_ordF, nsat_isStageF H (defOp H hP)]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

section Class

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP


theorem inL_trans {x y : V} (hx : InL H hP x) (hy : mem y x) : InL H hP y := by
  obtain ⟨a, S, ha, hS, hxS⟩ := hx
  exact ⟨a, S, ha, hS, isL_trans H hR hP ha hS x hxS y hy⟩

/-- Membership in `L_a` persists to larger stages. -/
theorem isL_le {a b S T x : V} (hb : Ord mem b) (hab : a = b ∨ mem a b) (hS : IsL H hP a S)
    (hT : IsL H hP b T) (hx : mem x S) : mem x T := by
  rcases hab with rfl | hab
  · rwa [isL_unique H hR hP hb hT hS]
  · exact isL_mono H hR hP hb hab hS hT x hx

/-- **Stage bounds.** A set of constructible sets lies in one stage. -/
theorem stage_bound {A : V} (hA : ∀ x, mem x A → InL H hP x) :
    ∃ b T, Ord mem b ∧ IsL H hP b T ∧ Sub mem A T := by
  let Q : V → V → Prop := fun x a => ∃ S, IsL H hP a S ∧ mem x S
  let Lst : V → V → Prop := fun x a => Ord mem a ∧ Q x a ∧ ∀ c, Ord mem c → Q x c → a = c ∨ mem a c
  have hLst : ∀ x, mem x A → ∃ a, Lst x a := by
    intro x hx
    obtain ⟨a, S, ha, hS, hxS⟩ := hA x hx
    exact least_ord H hR (Q x)
      (.ex 1 (.and (isStageF (defOp H hP) 0 1) (.mem 2 1))) (fun _ => x)
      (fun y => by
        simp only [NSat, nsat_isStageF H (defOp H hP)]
        simp (disch := omega) only [upd_same, upd_other]
        rfl) ha ⟨S, hS, hxS⟩
  obtain ⟨B, hB⟩ := repl_of H Lst
    (.and (ordF 0) (.and (.ex 2 (.and (isStageF (defOp H hP) 0 2) (.mem 1 2)))
      (.all 3 (.imp (.and (ordF 3) (.ex 4 (.and (isStageF (defOp H hP) 3 4) (.mem 1 4))))
        (.or (.eq 0 3) (.mem 0 3)))))) (fun _ => A)
    (fun x a => by
      simp only [NSat, nsat_ordF, nsat_isStageF H (defOp H hP), and_imp]
      simp (disch := omega) only [upd_same, upd_other]
      rfl)
    (fun x a1 a2 h1 h2 => (h1.2.2 a2 h2.1 h2.2.1).elim id fun h =>
      (h2.2.2 a1 h1.1 h1.2.1).elim Eq.symm fun h' =>
        absurd (h1.1.1 a2 h' a1 h) (mem_irrefl H hR a1)) A
  have hBord : ∀ a, mem a B → Ord mem a := fun a ha => ((hB a).1 ha).elim fun _ h => h.2.1
  have hβ := ord_vunion H hBord
  obtain ⟨T, hT⟩ := isL_exists H hR hP hβ
  refine ⟨_, T, hβ, hT, fun x hx => ?_⟩
  obtain ⟨a, hax⟩ := hLst x hx
  obtain ⟨S, hS, hxS⟩ := hax.2.1
  have haB : mem a B := (hB a).2 ⟨x, hx, hax⟩
  have hle := le_of_sub H hR hax.1 hβ fun w hw => (vunion_spec H B w).2 ⟨a, hw, haB⟩
  exact isL_le H hR hP hβ hle hS hT hxS

/-- Two constructible sets lie in one stage. -/
theorem stage_bound2 {x y : V} (hx : InL H hP x) (hy : InL H hP y) :
    ∃ b T, Ord mem b ∧ IsL H hP b T ∧ mem x T ∧ mem y T := by
  obtain ⟨b, T, hb, hT, hsub⟩ := stage_bound H hR hP (A := vpair H x y) fun z hz => by
    rcases (vpair_spec H x y z).1 hz with rfl | rfl <;> assumption
  exact ⟨b, T, hb, hT, hsub x ((vpair_spec H x y x).2 (Or.inl rfl)),
    hsub y ((vpair_spec H x y y).2 (Or.inr rfl))⟩

/-- A subset of a stage that is definable over it is constructible. -/
theorem inL_of_definable {b T S : V} (hb : Ord mem b) (hT : IsL H hP b T) (hsub : Sub mem S T)
    (hdef : DefinableIn H T S) : InL H hP S := by
  obtain ⟨T', hT'⟩ := isL_exists H hR hP (ord_succ H hb)
  exact ⟨_, T', ord_succ H hb, hT', (isL_spec H hR hP (ord_succ H hb) hT' S).2
    ⟨b, T, vsucc_self H b, hT, (gdef_spec H hP T S).2 ⟨hsub, Or.inr hdef⟩⟩⟩

omit hR hP in
/-- The internal environment `x, y, y, …` over `T`. -/
theorem env2 {T x y : V} (hx : mem x T) (hy : mem y T) :
    IsEnvOn H T (econs H x (constEnv H y)) ∧
      envVals H (econs H x (constEnv H y)) 0 = x ∧ envVals H (econs H x (constEnv H y)) 1 = y := by
  have he := constEnv_isEnvOn H (A := T) hy
  refine ⟨econs_isEnvOn H he hx, ?_, ?_⟩
  · rw [envVals_econs H he x 0]; rfl
  · rw [envVals_econs H he x 1]; exact constEnv_apply H (natV_mem_omega H 0)

/-! ### Pairing, Union and Power in L -/

theorem inL_pair {x y : V} (hx : InL H hP x) (hy : InL H hP y) : InL H hP (vpair H x y) := by
  obtain ⟨b, T, hb, hT, hxT, hyT⟩ := stage_bound2 H hR hP hx hy
  obtain ⟨he, h0, h1⟩ := env2 H hxT hyT
  refine inL_of_definable H hR hP hb hT (fun z hz => ?_) (definable_env H hP he
    (.fOr (.fEq 0 1) (.fEq 0 2)) _ fun z => ?_)
  · rcases (vpair_spec H x y z).1 hz with rfl | rfl <;> assumption
  · rw [vpair_spec H x y z]
    simp only [RSat, scons, h0, h1]
    constructor
    · rintro (rfl | rfl) <;> simp [*]
    · exact fun h => h.2

theorem inL_union {x : V} (hx : InL H hP x) : InL H hP (vunion H x) := by
  obtain ⟨b, T, hb, hT, hxT, -⟩ := stage_bound2 H hR hP hx hx
  obtain ⟨he, h0, -⟩ := env2 H hxT hxT
  have hTt := isL_trans H hR hP hb hT
  refine inL_of_definable H hR hP hb hT (fun z hz => ?_) (definable_env H hP he
    (.fEx (.fAnd (.fMem 0 2) (.fMem 1 0))) _ fun z => ?_)
  · obtain ⟨w, hzw, hwx⟩ := (vunion_spec H x z).1 hz
    exact hTt w (hTt x hxT w hwx) z hzw
  · rw [vunion_spec H x z]
    simp only [RSat, scons, h0]
    exact ⟨fun ⟨w, hzw, hwx⟩ => ⟨hTt w (hTt x hxT w hwx) z hzw, w, hTt x hxT w hwx, hwx, hzw⟩,
      fun ⟨_, w, _, hwx, hzw⟩ => ⟨w, hzw, hwx⟩⟩

/-- **Power in L**: the constructible subsets of a constructible set form a constructible set. -/
theorem inL_power {x : V} (hx : InL H hP x) :
    ∃ p, InL H hP p ∧ ∀ z, InL H hP z → (mem z p ↔ Sub mem z x) := by
  obtain ⟨P, hPx⟩ := hP x
  -- the constructible subsets of `x`
  obtain ⟨Q, hQ⟩ := sep_of H (InL H hP) (inLF H hP 0) (fun _ => x)
    (fun z => by rw [nsat_inLF H hP]; rfl) P
  obtain ⟨b, T, hb, hT, hQT⟩ := stage_bound H hR hP (A := vcup H Q (vsingle H x))
    (fun z hz => ((vcup_spec H Q _ z).1 hz).elim (fun hz => ((hQ z).1 hz).2) fun hz => by
      rwa [(vsingle_spec H x z).1 hz])
  have hxT : mem x T := hQT x ((vcup_spec H Q _ x).2 (Or.inr ((vsingle_spec H x x).2 rfl)))
  have hTt := isL_trans H hR hP hb hT
  obtain ⟨he, h0, -⟩ := env2 H hxT hxT
  obtain ⟨p, hp⟩ := sep_of H (fun z => Sub mem z x) (subF 0 1) (fun _ => x)
    (fun z => by rw [nsat_subF]; rfl) T
  refine ⟨p, inL_of_definable H hR hP hb hT (fun z hz => ((hp z).1 hz).1)
    (definable_env H hP he (.fAll (.fImp (.fMem 0 1) (.fMem 0 2))) p fun z => ?_), fun z hz => ?_⟩
  · rw [hp z]
    refine and_congr_right fun hzT => ?_
    simp only [RSat, scons, h0]
    exact ⟨fun h w _ hw => h w hw, fun h w hw => h w (hTt z hzT w hw) hw⟩
  · rw [hp z]
    exact ⟨fun h => h.2, fun h => ⟨hQT z ((vcup_spec H Q _ z).2 (Or.inl ((hQ z).2
      ⟨(hPx z).2 h, hz⟩))), h⟩⟩

end Class

end SetTheory.BusyBeaver.ZFC.Constructible
