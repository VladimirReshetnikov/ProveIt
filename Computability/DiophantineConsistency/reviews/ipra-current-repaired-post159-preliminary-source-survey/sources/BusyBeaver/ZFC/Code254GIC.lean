import BusyBeaver.ZFC.Code254Containers
import BusyBeaver.ZFC.ProfileModel

/-!
Hygienic de Bruijn matrices for the original encoded bundle theory.

Free slot i uses odd name 2*i+1. At depth d a new bound variable uses
even name 2*d, disjoint from every earlier name. Relative falsity is the
atom Rel(0,0); global irreflexivity validates it under every binder.
This is a model adapter, not an enumerator or binary-machine theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254GIC

open Tarski (NF)
open Code254Containers

universe u
variable {V : Type u}

def names : Nat → Nat → Nat
  | 0, i => 2 * i + 1
  | d + 1, 0 => 2 * d
  | d + 1, i + 1 => names d i

theorem names_ne_future (d i k : Nat) (h : d ≤ k) : names d i ≠ 2 * k := by
  induction d generalizing i k with
  | zero => simp only [names]; omega
  | succ d ih =>
    cases i with
    | zero => simp only [names]; omega
    | succ i => exact ih i k (by omega)

def toNamed (d : Nat) : Form → NF
  | .fMem i j => .rel (names d i) (names d j)
  | .fEq i j => .eq (names d i) (names d j)
  | .fBot => falsity
  | .fImp f g => .imp (toNamed d f) (toNamed d g)
  | .fAnd f g => conj (toNamed d f) (toNamed d g)
  | .fOr f g => .imp (Code254Containers.neg (toNamed d f)) (toNamed d g)
  | .fAll f => .all (2 * d) (toNamed (d + 1) f)
  | .fEx f => ex (2 * d) (toNamed (d + 1) f)

theorem botFree_toNamed (f : Form) (d : Nat) : Tarski.BotFree (toNamed d f) := by
  induction f generalizing d <;>
    simp [toNamed, Tarski.BotFree, conj, Code254Containers.neg, ex, falsity, NF.exF, *]

theorem relate_under (d : Nat) (e e' : Nat → V) (x : V)
    (h : ∀ i, e' (names d i) = e i) :
    ∀ i, Tarski.update e' (2 * d) x (names (d + 1) i) = scons x e i := by
  intro i
  cases i with
  | zero => simp [names, Tarski.update, scons]
  | succ i =>
    simpa only [names, Tarski.update, if_neg (names_ne_future d i d (Nat.le_refl d)), scons]
      using h i

theorem sat_disj (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (f g : NF) :
    Tarski.Sat mem e (.imp (Code254Containers.neg f) g) ↔
      Tarski.Sat mem e f ∨ Tarski.Sat mem e g := by
  change ((Tarski.Sat mem e f → mem (e 0) (e 0)) → Tarski.Sat mem e g) ↔ _
  constructor
  · intro h
    by_cases hf : Tarski.Sat mem e f
    · exact Or.inl hf
    · exact Or.inr (h (fun h' => (hf h').elim))
  · exact fun h hn => h.elim (fun hf => (hirr _ (hn hf)).elim) id

/-- Every source environment has the intended interpretation under its name map. -/
theorem sat_toNamed (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (f : Form) (d : Nat) (e e' : Nat → V)
    (h : ∀ i, e' (names d i) = e i) :
    Tarski.Sat mem e' (toNamed d f) ↔ SetTheory.Sat mem e f := by
  induction f generalizing d e e' with
  | fMem i j | fEq i j => simp only [toNamed, Tarski.Sat, SetTheory.Sat, h i, h j]
  | fBot =>
    change mem (e' 0) (e' 0) ↔ False
    exact ⟨hirr _, False.elim⟩
  | fImp f g ihf ihg => exact imp_congr (ihf d e e' h) (ihg d e e' h)
  | fAnd f g ihf ihg =>
    exact (sat_conj mem hirr e' _ _).trans (and_congr (ihf d e e' h) (ihg d e e' h))
  | fOr f g ihf ihg =>
    exact (sat_disj mem hirr e' _ _).trans (or_congr (ihf d e e' h) (ihg d e e' h))
  | fAll f ih =>
    exact forall_congr' (fun x => ih (d + 1) (scons x e)
      (Tarski.update e' (2 * d) x) (relate_under d e e' x h))
  | fEx f ih =>
    exact (sat_ex mem hirr e' _ _).trans (exists_congr (fun x =>
      ih (d + 1) (scons x e) (Tarski.update e' (2 * d) x) (relate_under d e e' x h)))

theorem enc_pos (f : NF) : 0 < Code254.enc f := by
  induction f with
  | rel i j => simp only [Code254.enc, Code254.wel]; omega
  | eq i j => simp only [Code254.enc, Code254.weq]; omega
  | bot => decide
  | imp f g hf hg =>
    have hp := Code254.le_P_left (Code254.enc f) (Code254.enc g)
    simp only [Code254.enc, Code254.wim]
    omega
  | all i f hf => simp only [Code254.enc, Code254.wal]; omega

/-- Bound and free labels are strictly smaller than a finite formula's code. -/
theorem occurs_lt_enc (f : NF) (i : Nat) (h : NF.Occurs i f) : i < Code254.enc f := by
  induction f with
  | rel a b =>
    have ha := Code254.le_P_left a b
    have hb := Code254.le_P_right a b
    simp only [NF.Occurs] at h
    simp only [Code254.enc, Code254.wel]
    rcases h with h | h <;> omega
  | eq a b =>
    have ha := Code254.le_P_left a b
    have hb := Code254.le_P_right a b
    simp only [NF.Occurs] at h
    simp only [Code254.enc, Code254.weq]
    rcases h with h | h <;> omega
  | bot => exact h.elim
  | imp f g hf hg =>
    have ha := Code254.le_P_left (Code254.enc f) (Code254.enc g)
    have hb := Code254.le_P_right (Code254.enc f) (Code254.enc g)
    simp only [NF.Occurs] at h
    simp only [Code254.enc, Code254.wim]
    rcases h with h | h
    · have := hf h; omega
    · have := hg h; omega
  | all a f hf =>
    have ha := Code254.le_P_left a (Code254.enc f)
    have hb := Code254.le_P_right a (Code254.enc f)
    simp only [NF.Occurs] at h
    simp only [Code254.enc, Code254.wal]
    rcases h with h | h
    · omega
    · have := hf h; omega

theorem not_free_enc (f : NF) : ¬ NF.Free (Code254.enc f) f := by
  intro h
  have := occurs_lt_enc f (Code254.enc f) (NF.Free.occurs h)
  omega

/-- Equivalent padding also makes the code larger than the chosen names1,3. -/
def pad (f : NF) : NF := .imp (.imp f f) f

theorem botFree_pad (f : NF) (h : Tarski.BotFree f) : Tarski.BotFree (pad f) :=
  ⟨⟨h, h⟩, h⟩

theorem sat_pad (mem : V → V → Prop) (e : Nat → V) (f : NF) :
    Tarski.Sat mem e (pad f) ↔ Tarski.Sat mem e f :=
  ⟨fun h => h (fun h' => h'), fun h _ => h⟩

theorem pad_code_gt_three (f : NF) : 3 < Code254.enc (pad f) := by
  have hf := enc_pos f
  have hp := Code254.le_P_left (Code254.enc f) (Code254.enc f)
  have hinner : 4 ≤ Code254.enc (.imp f f) := by
    change 4 ≤ 4 * Code254.P (Code254.enc f) (Code254.enc f)
    omega
  have hp' := Code254.le_P_left (Code254.enc (.imp f f)) (Code254.enc f)
  change 3 < 4 * Code254.P (Code254.enc (.imp f f)) (Code254.enc f)
  omega

theorem bundle_mem (a b : Nat) (f : NF) (h : Tarski.BotFree f)
    (ha : Code254.enc f ≠ a) (hb : Code254.enc f ≠ b) :
    Code254.EncBundle (namedBundle a b (Code254.enc f) f) :=
  ⟨botFree_namedBundle a b (Code254.enc f) f h,
    a, b, Code254.enc f, ha, hb, enc_namedBundle a b f⟩

theorem namedG_of_model (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (f : NF) (h : Tarski.BotFree f) (e : Nat → V) :
    Tarski.Sat mem e (namedG 1 3 (Code254.enc (pad f)) (pad f)) := by
  have hc := pad_code_gt_three f
  have hall := hB _ (bundle_mem 1 3 (pad f) (botFree_pad f h) (by omega) (by omega)) e
  exact ((sat_conj mem hirr e _ _).mp ((sat_conj mem hirr e _ _).mp hall).1).2

def namedRelation (mem : V → V → Prop) (f : NF) (e : Nat → V) (x y : V) : Prop :=
  Tarski.Sat mem (Tarski.update (Tarski.update e 1 x) 3 y) f

private theorem free_ne (f : NF) (c : Nat) (h : ¬ NF.Free c f)
    (n : Nat) (hn : NF.Free n f) : n ≠ c :=
  fun he => h (he ▸ hn)

theorem forward_matrix (mem : V → V → Prop) (f : NF) (e : Nat → V)
    (c : Nat) (v x y : V) (h : ¬ NF.Free c f) :
    Tarski.Sat mem (Tarski.update (Tarski.update (Tarski.update e c v) 1 x) 3 y) f ↔
      namedRelation mem f e x y := by
  apply Tarski.sat_ext
  intro n hn
  simp [Tarski.update, free_ne f c h n hn]

theorem support_matrix (mem : V → V → Prop) (f : NF) (e : Nat → V)
    (c : Nat) (v x y : V) (h : ¬ NF.Free c f) :
    Tarski.Sat mem (Tarski.update (Tarski.update (Tarski.update e c v) 3 y) 1 x) f ↔
      namedRelation mem f e x y := by
  apply Tarski.sat_ext
  intro n hn
  have hnc := free_ne f c h n hn
  by_cases h1 : n = 1
  · subst n; simp [Tarski.update]
  · by_cases h3 : n = 3
    · subst n; simp [Tarski.update]
    · simp [Tarski.update, h1, h3, hnc]

theorem selected_matrix (mem : V → V → Prop) (f : NF) (e : Nat → V)
    (c : Nat) (v x y z : V) (h : ¬ NF.Free c f) :
    Tarski.Sat mem (Tarski.update
      (Tarski.update (Tarski.update (Tarski.update e c v) 1 x) 3 y) 3 z) f ↔
      namedRelation mem f e x z := by
  apply Tarski.sat_ext
  intro n hn
  have hnc := free_ne f c h n hn
  by_cases h3 : n = 3
  · subst n; simp [Tarski.update]
  · simp [Tarski.update, h3, hnc]

/-- Exact collection at the domain held in name3, from the literal G tree. -/
theorem collection_at_of_namedG (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (f : NF) (e : Nat → V) (c : Nat) (h1 : c ≠ 1) (h3 : c ≠ 3)
    (hf : ¬ NF.Free c f) (h : Tarski.Sat mem e (namedG 1 3 c f)) :
    ∃ v, ProfileCollection.ImageCollection mem (namedRelation mem f e) (e 3) v := by
  obtain ⟨v, hv⟩ := (sat_ex mem hirr e c _).mp h
  have hg := (sat_conj mem hirr (Tarski.update e c v) _ _).mp hv
  refine ⟨v, ?_, ?_⟩
  · intro y hy
    have hy' : Tarski.Sat mem (Tarski.update (Tarski.update e c v) 3 y) (.rel 3 c) := by
      simpa [Tarski.Sat, Tarski.update, h3] using hy
    obtain ⟨x, hxy⟩ := (sat_ex mem hirr _ 1 _).mp (hg.2 y hy')
    exact ⟨x, (support_matrix mem f e c v x y hf).mp hxy⟩
  · rintro x hx ⟨y, hxy⟩
    have hx' : Tarski.Sat mem (Tarski.update (Tarski.update e c v) 1 x) (.rel 1 3) := by
      simpa [Tarski.Sat, Tarski.update, Ne.symm h3] using hx
    have hxy' := (forward_matrix mem f e c v x y hf).mpr hxy
    obtain ⟨z, hz⟩ := (sat_ex mem hirr _ 3 _).mp (hg.1 x hx' y hxy')
    have hz' := (sat_conj mem hirr _ _ _).mp hz
    refine ⟨z, ?_, (selected_matrix mem f e c v x y z hf).mp hz'.1⟩
    simpa [Tarski.Sat, Tarski.update, h1, h3] using hz'.2

theorem domain_relation (mem : V → V → Prop) (f : NF) (e : Nat → V) (a x y : V) :
    namedRelation mem f (Tarski.update e 3 a) x y ↔ namedRelation mem f e x y := by
  apply Tarski.sat_ext
  intro n _
  by_cases h3 : n = 3
  · subst n; simp [Tarski.update]
  · simp [Tarski.update, h3]

/-- Every named matrix supplies an actual collection instance, with both gates charged. -/
theorem collection_of_model (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (f : NF) (h : Tarski.BotFree f) (e : Nat → V) :
    ProfileCollection.CollectionInstance mem (namedRelation mem (pad f) e) := by
  intro a
  let ea := Tarski.update e 3 a
  have hc := pad_code_gt_three f
  obtain ⟨v, hs, hv⟩ := collection_at_of_namedG mem hirr (pad f) ea
    (Code254.enc (pad f)) (by omega) (by omega) (not_free_enc (pad f))
    (namedG_of_model mem hirr hB f h ea)
  refine ⟨v, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := hs y hy
    exact ⟨x, (domain_relation mem (pad f) e a x y).mp hxy⟩
  · rintro x hx ⟨y, hxy⟩
    obtain ⟨z, hz, hxz⟩ := hv x (by simpa [ea, Tarski.update] using hx)
      ⟨y, (domain_relation mem (pad f) e a x y).mpr hxy⟩
    exact ⟨z, hz, (domain_relation mem (pad f) e a x z).mp hxz⟩

/-- Odd names5,7,... hold parameters; the first two source slots are overridden. -/
def parameterEnv (witness : V) (env : Nat → V) (n : Nat) : V :=
  if n < 5 then witness else env ((n - 5) / 2)

theorem parameterEnv_slots (witness : V) (env : Nat → V) (x y : V) :
    ∀ i, Tarski.update (Tarski.update (parameterEnv witness env) 1 x) 3 y (names 0 i) =
      scons x (scons y env) i := by
  intro i
  cases i with
  | zero => simp [names, Tarski.update, scons]
  | succ i =>
    cases i with
    | zero => simp [names, Tarski.update, scons]
    | succ k =>
      have h1 : 2 * (k + 2) + 1 ≠ 1 := by omega
      have h3 : 2 * (k + 2) + 1 ≠ 3 := by omega
      have h5 : ¬ 2 * (k + 2) + 1 < 5 := by omega
      have hk : (2 * (k + 2) + 1 - 5) / 2 = k := by omega
      simpa [names, Tarski.update, parameterEnv, scons, h1, h3, h5] using congrArg env hk

theorem matrix_relation (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (f : Form) (witness : V) (env : Nat → V) (x y : V) :
    namedRelation mem (pad (toNamed 0 f)) (parameterEnv witness env) x y ↔
      DeepPositiveClosure.MatrixRelation mem f env x y :=
  (sat_pad mem _ _).trans (sat_toNamed mem hirr f 0 _ _ (parameterEnv_slots witness env x y))

/-- Every actual Form matrix is supplied; no semantic-relation schema is assumed. -/
theorem collection_of_matrix (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (valuation : Nat → V)
    (hB : ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (f : Form) (env : Nat → V) :
    ProfileCollection.CollectionInstance mem (DeepPositiveClosure.MatrixRelation mem f env) :=
  ProfileModel.collectionInstance_congr mem _ _
    (matrix_relation mem hirr f (valuation 0) env)
    (collection_of_model mem hirr hB (toNamed 0 f) (botFree_toNamed f 0)
      (parameterEnv (valuation 0) env))

theorem modelsGIC_of_encBundle (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (valuation : Nat → V)
    (hB : ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    ProfileModel.ModelsGIC mem :=
  fun f _ env => (ProfileSyntax.sat_gicForm mem f env).mpr
    (collection_of_matrix mem hirr valuation hB f env)

/-- The EncBundle theory supplies the existing equality-free CP/GIC model interface. -/
theorem modelsCPGIC_of_encBundle (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (valuation : Nat → V)
    (hB : ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    ProfileModel.ModelsCPGIC mem :=
  ⟨fun env => (ProfileModel.sat_containerForm mem env).mpr
      (containers_of_encBundle mem hirr valuation hB),
    modelsGIC_of_encBundle mem hirr valuation hB⟩

end SetTheory.BusyBeaver.ZFC.Code254GIC
