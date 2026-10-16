import BusyBeaver.ZFC.ProfileModel
import BusyBeaver.ZFC.Code254Models

/-!
A conditional obstruction to the reverse numerical-model comparison.

Duplicating every object preserves actual equality-free CP/GIC and
irreflexivity. It destroys literal native singletons, whereas the single
numeric GIC matrix Eq(1,2), code35, requires such a singleton. Thus the
equality-free model interface cannot alone supply all decoded bundles.

The starting model and a domain witness are explicit parameters. No
existence or consistency of that model is assumed as a theorem here.
-/

namespace SetTheory.BusyBeaver.ZFC.DuplicateProfiles

open DeepPositiveClosure ProfileModel ProfileSyntax ProfileCollection

universe u
variable {V : Type u}

def duplicateMem (mem : V → V → Prop) (x y : V × Bool) : Prop :=
  mem x.1 y.1

theorem project_scons (env : Nat → V × Bool) (x : V × Bool) :
    (fun i => (scons x env i).1) = scons x.1 (fun i => (env i).1) := by
  funext i
  cases i <;> rfl

/-- Equality-free actual formulas see only the first coordinates. -/
theorem sat_duplicate (mem : V → V → Prop) (phi : Form) (h : EqualityFree phi)
    (env : Nat → V × Bool) :
    Sat (duplicateMem mem) env phi ↔ Sat mem (fun i => (env i).1) phi := by
  induction phi generalizing env with
  | fMem i j => exact Iff.rfl
  | fEq i j => exact h.elim
  | fBot => exact Iff.rfl
  | fImp phi psi ihp ihq => exact imp_congr (ihp h.1 env) (ihq h.2 env)
  | fAnd phi psi ihp ihq => exact and_congr (ihp h.1 env) (ihq h.2 env)
  | fOr phi psi ihp ihq => exact or_congr (ihp h.1 env) (ihq h.2 env)
  | fAll phi ih =>
    constructor
    · intro hall x
      simpa only [project_scons] using
        (ih h (scons (x, false) env)).mp (hall (x, false))
    · intro hall x
      apply (ih h (scons x env)).mpr
      simpa only [project_scons] using hall x.1
  | fEx phi ih =>
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.1, by simpa only [project_scons] using (ih h (scons x env)).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨(x, false), (ih h (scons (x, false) env)).mpr
        (by simpa only [project_scons] using hx)⟩

theorem irreflexive_duplicate (mem : V → V → Prop) (h : ∀ x, ¬ mem x x) :
    ∀ x, ¬ duplicateMem mem x x := fun x => h x.1

/-- This transfers the literal formula-indexed schema, rather than a schema
for arbitrary semantic predicates. -/
theorem models_duplicate (mem : V → V → Prop) (h : ModelsCPGIC mem) :
    ModelsCPGIC (duplicateMem mem) := by
  constructor
  · intro env
    exact (sat_duplicate mem containerForm equalityFree_containerForm env).mpr (h.1 _)
  · intro phi hphi env
    exact (sat_duplicate mem (gicForm phi) (equalityFree_gicForm phi hphi) env).mpr
      (h.2 phi hphi _)

/-- The two tagged copies have identical outgoing membership profiles. -/
theorem outgoing_twins (mem : V → V → Prop) (p : V) (z : V × Bool) :
    duplicateMem mem (p, false) z ↔ duplicateMem mem (p, true) z := Iff.rfl

theorem no_native_singleton (mem : V → V → Prop) (p : V × Bool) :
    ¬ ∃ s, ∀ y, duplicateMem mem y s ↔ y = p := by
  rintro ⟨s, hs⟩
  have hp : duplicateMem mem p s := (hs p).mpr rfl
  let q : V × Bool := (p.1, Bool.not p.2)
  have hq : duplicateMem mem q s := hp
  have heq := congrArg Prod.snd ((hs q).mp hq)
  change Bool.not p.2 = p.2 at heq
  cases htag : p.2 <;> simp [htag] at heq

/-- One constant native-equality collection matrix forces a literal singleton. -/
theorem singleton_of_point_collection (mem : V → V → Prop) (p A : V)
    (hpA : mem p A) (h : CollectionInstance mem (fun _ y => y = p)) :
    ∃ s, ∀ y, mem y s ↔ y = p := by
  obtain ⟨s, hs, hc⟩ := h A
  obtain ⟨z, hzs, rfl⟩ := hc p hpA ⟨p, rfl⟩
  refine ⟨s, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    exact (hs y hy).choose_spec
  · rintro rfl
    exact hzs

/-- The failed relation is supplied by this single actual native-Eq matrix. -/
theorem point_collection_of_form (mem : V → V → Prop) (p : V)
    (h : Sat mem (fun _ => p) (gicForm (.fEq 1 2))) :
    CollectionInstance mem (fun _ y => y = p) := by
  exact collectionInstance_congr mem _ _ (fun _ _ => Iff.rfl)
    ((sat_gicForm mem (.fEq 1 2) (fun _ => p)).mp h)

/-- Even this one equality-bearing actual schema instance fails in the
duplicate. Irreflexivity is not needed for this first-order obstruction. -/
theorem duplicate_not_point_gic (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) :
    ¬ Sat (duplicateMem mem) (fun _ => (witness, false)) (gicForm (.fEq 1 2)) := by
  intro hPoint
  obtain ⟨A, hpA, _, _⟩ :=
    ((sat_containerForm mem (fun _ => witness)).mp (h.1 _)) witness
  exact no_native_singleton mem (witness, false)
    (singleton_of_point_collection (duplicateMem mem) (witness, false) (A, false) hpA
      (point_collection_of_form (duplicateMem mem) (witness, false) hPoint))

open Tarski Tarski.NF Code254Containers

theorem point_code : Code254.enc (.eq 1 2) = 35 := by decide

def singletonCarrier : NF := namedBundle 0 1 35 (.eq 1 2)

theorem singletonCarrier_mem : Code254.EncBundle singletonCarrier := by
  refine ⟨botFree_namedBundle 0 1 35 (.eq 1 2) True.intro,
    0, 1, 35, by decide, by decide, ?_⟩
  exact (by simpa only [singletonCarrier, point_code] using enc_namedBundle 0 1 (.eq 1 2))

/-- Native Eq in the literal fixed G tree produces the same singleton. -/
theorem singleton_of_namedG (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (env : Nat → V) (hA : ∃ x, mem x (env 1))
    (h : Tarski.Sat mem env (namedG 0 1 35 (.eq 1 2))) :
    ∃ s, ∀ y, mem y s ↔ y = env 2 := by
  obtain ⟨s, hs⟩ := (sat_ex mem hirr env 35 _).mp h
  obtain ⟨hc, hsup⟩ := (sat_conj mem hirr (update env 35 s) _ _).mp hs
  have hSupport : ∀ y, mem y s → y = env 2 := by
    intro y hy
    have hy' : Tarski.Sat mem (update (update env 35 s) 1 y) (.rel 1 35) := by
      simpa [Tarski.Sat, update] using hy
    obtain ⟨x, hx⟩ := (sat_ex mem hirr _ 0 _).mp (hsup y hy')
    simpa [Tarski.Sat, update] using hx
  obtain ⟨x, hx⟩ := hA
  have hx' : Tarski.Sat mem (update (update env 35 s) 0 x) (.rel 0 1) := by
    simpa [Tarski.Sat, update] using hx
  have hp' : Tarski.Sat mem (update (update (update env 35 s) 0 x) 1 (env 2))
      (.eq 1 2) := by simp [Tarski.Sat, update]
  obtain ⟨z, hz⟩ := (sat_ex mem hirr _ 1 _).mp (hc x hx' (env 2) hp')
  obtain ⟨hzp, hzs⟩ := (sat_conj mem hirr _ _ _).mp hz
  have hzp' : z = env 2 := by simpa [Tarski.Sat, update] using hzp
  have hzs' : mem z s := by simpa [Tarski.Sat, update] using hzs
  refine ⟨s, fun y => ⟨hSupport y, ?_⟩⟩
  rintro rfl
  exact hzp' ▸ hzs'

theorem singleton_of_encodable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : Code254Models.ModelsEncodable mem) (env : Nat → V)
    (hA : ∃ x, mem x (env 1)) :
    ∃ s, ∀ y, mem y s ↔ y = env 2 := by
  have hB := h singletonCarrier singletonCarrier_mem env
  have hCG := ((sat_conj mem hirr env _ _).mp hB).1
  have hG := ((sat_conj mem hirr env _ _).mp hCG).2
  exact singleton_of_namedG mem hirr env hA hG

/-- Assuming an inhabited irreflexive starting CP/GIC model, its duplicate is an
irreflexive CP/GIC model that fails the actual numerical model obligation. -/
theorem duplicate_not_decoded (mem : V → V → Prop) (witness : V)
    (hirr : ∀ x, ¬ mem x x) (h : ModelsCPGIC mem) :
    ¬ Code254Models.ModelsDecoded (duplicateMem mem) := by
  intro hDecoded
  obtain ⟨A, hpA, _, _⟩ :=
    ((sat_containerForm mem (fun _ => witness)).mp (h.1 _)) witness
  let p : V × Bool := (witness, false)
  let env : Nat → V × Bool := fun n => if n = 1 then (A, false) else p
  have hA : ∃ x, duplicateMem mem x (env 1) := by
    exact ⟨p, hpA⟩
  have hEnc := Code254Models.encodable_of_decoded (duplicateMem mem)
    (irreflexive_duplicate mem hirr) hDecoded
  exact no_native_singleton mem (env 2)
    (singleton_of_encodable (duplicateMem mem) (irreflexive_duplicate mem hirr) hEnc env hA)

/-- All three assertions use this same explicitly constructed duplicate. -/
theorem duplicate_obstruction (mem : V → V → Prop) (witness : V)
    (hirr : ∀ x, ¬ mem x x) (h : ModelsCPGIC mem) :
    ModelsCPGIC (duplicateMem mem) ∧
      (∀ x, ¬ duplicateMem mem x x) ∧
      ¬ Code254Models.ModelsDecoded (duplicateMem mem) :=
  ⟨models_duplicate mem h, irreflexive_duplicate mem hirr,
    duplicate_not_decoded mem witness hirr h⟩

end SetTheory.BusyBeaver.ZFC.DuplicateProfiles
