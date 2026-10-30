import BusyBeaver.ZFC.KLowerRel

/-!
Exact comprehension in the tagged domain (Elliot Glazer's `KMarkers`, `KDomain`,
`KDSeparation`).

Fix a raw empty marker `t`. For a raw bound `U ≠ t` the *envelope* `{U} ∪ {z ∈ U | t ∈ z}` is
untagged and contains every tagged member of `U`; tagged comprehension over it,
`{E, t} ∪ {z ∈ E | z ∈ U ∧ θ z}`, is a tagged set whose tagged members are exactly the tagged
members of `U` satisfying `θ`: its two extra members `E` and `t` are untagged, hence invisible in
`D_t` (`dt_comp`). With `U` a raw pair, union bound, power set or transitive container this gives
pairing, union, power and transitive containers in `D_t`; with `U = a` it is separation for every
formula over the tagged domain (`tag_sep`).
-/

namespace SetTheory.BusyBeaver.ZFC.KLower

open SetTheory.BusyBeaver.ZFC.KSeed222 Form

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Swap the first two slots. -/
def swap01 : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

section Tagged

variable (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V} (ht : ∀ z, ¬ mem z t)
include hs hirr ht

/-- **Comprehension in `D_t` over a raw bound.** -/
theorem dt_comp (U : V) (θ : Form) (ρ : Nat → V) :
    ∃ S, mem t S ∧ ∀ z, mem t z → (mem z S ↔ mem z U ∧ Sat mem (scons z ρ) θ) := by
  by_cases hU : U = t
  · subst hU
    obtain ⟨S, hS⟩ := raw_singleton hs U
    refine ⟨S, (hS U).mpr rfl, fun z hz => ⟨fun hzS => ?_, fun h => (ht z h.1).elim⟩⟩
    have : z = U := (hS z).mp hzS
    exact (hirr U (this ▸ hz)).elim
  · -- the envelope of `U`
    obtain ⟨E, hE⟩ := raw_aug hs hirr U (fMem 1 0) (scons t (fun _ => t))
    have hEt : E ≠ t := fun e => ht U (e ▸ (hE U).mpr (Or.inl rfl))
    have htE : ¬ mem t E := fun h => by
      rcases (hE t).mp h with h | ⟨-, h⟩
      · exact hU h.symm
      · exact hirr t h
    have hθ : ∀ z, Sat mem (scons z (scons U ρ)) (rename (shiftAfter 0) θ) ↔ Sat mem (scons z ρ) θ :=
      fun z => Sat_rename_ext θ _ _ _ fun n => by cases n <;> rfl
    obtain ⟨S, hS⟩ := raw_tagged hs hirr ht E hEt (fAnd (fMem 0 1) (rename (shiftAfter 0) θ))
      (scons U ρ)
    refine ⟨S, (hS t).mpr (Or.inr (Or.inl rfl)), fun z hz => ?_⟩
    have hzE : z ≠ E := fun e => htE (e ▸ hz)
    have hzt : z ≠ t := fun e => hirr t (e ▸ hz)
    rw [hS z]
    constructor
    · rintro (h | h | ⟨-, hzU, hθz⟩)
      · exact absurd h hzE
      · exact absurd h hzt
      · exact ⟨hzU, (hθ z).mp hθz⟩
    · rintro ⟨hzU, hθz⟩
      exact Or.inr (Or.inr ⟨(hE z).mpr (Or.inr ⟨hzU, hz⟩), hzU, (hθ z).mpr hθz⟩)

/-- A tagged set exists. -/
theorem tag_inhabited : ∃ x, mem t x := by
  obtain ⟨s, hs'⟩ := raw_singleton hs t
  exact ⟨s, (hs' t).mpr rfl⟩

end Tagged

/-! ## Statements in the tagged domain -/

section TagWorld

variable (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V} (ht : ∀ z, ¬ mem z t)
include hs hirr ht

/-- From a raw bound containing the wanted tagged members to a tagged set. -/
theorem tag_of_bound (U : V) (P : Tag mem t → Prop) (θ : Form) (ρ : Nat → V)
    (hP : ∀ z : Tag mem t, P z ↔ mem z.1 U ∧ Sat mem (scons z.1 ρ) θ) :
    ∃ S : Tag mem t, ∀ z : Tag mem t, tmem mem t z S ↔ P z := by
  obtain ⟨S, htS, hS⟩ := dt_comp hs hirr ht U θ ρ
  exact ⟨⟨S, htS⟩, fun z => (hS z.1 z.2).trans (hP z).symm⟩

/-- **Separation in `D_t`**, for every formula over the tagged domain. -/
theorem tag_sep (a : Tag mem t) (φ : Form) (env : Nat → Tag mem t) :
    ∃ s : Tag mem t, ∀ z, tmem mem t z s ↔ tmem mem t z a ∧ Sat (tmem mem t) (scons z env) φ := by
  apply tag_of_bound hs hirr ht a.1 _ (rename swap01 (relT 0 φ)) (scons t (fun i => (env i).1))
  intro z
  refine and_congr Iff.rfl ?_
  rw [sat_top]
  exact (Sat_rename_ext _ _ _ _ fun n => by rcases n with _ | _ | _ <;> rfl).symm

/-- Pairing in `D_t`. -/
theorem tag_pair (a b : Tag mem t) :
    ∃ p : Tag mem t, ∀ z, tmem mem t z p ↔ z = a ∨ z = b := by
  obtain ⟨U, hU⟩ := raw_pair hs ht a.1 b.1
  apply tag_of_bound hs hirr ht U _ (fEq 0 0) (fun _ => t)
  intro z
  refine ⟨fun h => ⟨(hU z.1).mpr (h.imp (congrArg Subtype.val) (congrArg Subtype.val)), rfl⟩, fun h => ?_⟩
  rcases (hU z.1).mp h.1 with h' | h'
  · exact Or.inl (Subtype.ext h')
  · exact Or.inr (Subtype.ext h')

/-- Union in `D_t`. -/
theorem tag_union (a : Tag mem t) :
    ∃ w : Tag mem t, ∀ z, tmem mem t z w ↔ ∃ y, tmem mem t z y ∧ tmem mem t y a := by
  obtain ⟨v, hav, hv⟩ := raw_transitive hs a.1
  -- z ∈ y ∈ a with y tagged, read raw: ∃ y (t ∈ y ∧ z ∈ y ∧ y ∈ a)
  apply tag_of_bound hs hirr ht v _
    (fEx (fAnd (fMem 2 0) (fAnd (fMem 1 0) (fMem 0 3)))) (scons t (scons a.1 (fun _ => t)))
  intro z
  constructor
  · rintro ⟨y, hzy, hya⟩
    exact ⟨hv y.1 (hv a.1 hav y.1 hya) z.1 hzy, y.1, y.2, hzy, hya⟩
  · rintro ⟨-, y, hty, hzy, hya⟩
    exact ⟨⟨y, hty⟩, hzy, hya⟩

/-- Transitive containers in `D_t`. -/
theorem tag_transitive (a : Tag mem t) :
    ∃ v : Tag mem t, tmem mem t a v ∧ ∀ y, tmem mem t y v → ∀ z, tmem mem t z y → tmem mem t z v := by
  obtain ⟨U, haU, hU⟩ := raw_transitive hs a.1
  obtain ⟨v, hv⟩ := tag_of_bound hs hirr ht U (fun z => mem z.1 U) (fEq 0 0) (fun _ => t)
    (fun z => ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩)
  exact ⟨v, (hv a).mpr haU, fun y hy z hz => (hv z).mpr (hU y.1 ((hv y).mp hy) z.1 hz)⟩

/-- Slots of the collection matrix's guarded formula (Elliot Glazer's `KCollection`):
marker `5`, output `1`, input `0`, parameters from `6`. -/
def collSh : Nat → Nat
  | 0 => 5
  | 1 => 1
  | 2 => 0
  | n + 3 => n + 6

/-- **Collection in `D_t`** for every formula over the tagged domain: a tagged set of images,
with an image of each tagged member of `a` that has one. -/
theorem tag_collection (φ : Form) (env : Nat → Tag mem t) (a : Tag mem t) :
    ∃ b : Tag mem t, ProfileCollection.ImageCollection (tmem mem t)
      (fun x y => Sat (tmem mem t) (scons y (scons x env)) φ) a b := by
  let vals : Nat → V := fun i => (env i).1
  have hR : ∀ x y : Tag mem t, Sat (tmem mem t) (scons y (scons x env)) φ ↔
      Sat mem (scons t (scons y.1 (scons x.1 vals))) (relT 0 φ) := by
    intro x y
    rw [sat_top]
    have e : topEnv t (scons y (scons x env)) = scons t (scons y.1 (scons x.1 vals)) :=
      funext fun n => by rcases n with _ | _ | _ | n <;> rfl
    rw [e]
  -- the envelope of `a` and the root pair
  obtain ⟨E, hE⟩ := raw_aug hs hirr a.1 (fMem 1 0) (scons t (fun _ => t))
  have hat : a.1 ≠ t := fun e => hirr t (by have h := a.2; rw [e] at h; exact h)
  have hEt : E ≠ t := fun e => ht a.1 (e ▸ (hE a.1).mpr (Or.inl rfl))
  have htE : ¬ mem t E := fun h => by
    rcases (hE t).mp h with h | ⟨-, h⟩
    · exact hat h.symm
    · exact hirr t h
  obtain ⟨r0, hr0⟩ := raw_pair hs ht E t
  have hr0t : r0 ≠ t := fun e => ht E (e ▸ (hr0 E).mpr (Or.inl rfl))
  have hr0s : ∀ v, ¬ IsSing mem r0 v := fun v hv =>
    hEt ((hv E).mp ((hr0 E).mpr (Or.inl rfl)) ▸ ((hv t).mp ((hr0 t).mpr (Or.inr rfl))).symm)
  have hts : ∀ v, ¬ IsSing mem t v := fun v hv => ht v ((hv v).mpr rfl)
  let renv : Nat → V := scons r0 (scons E (scons t vals))
  have hθ : ∀ (x' v u : V), Sat mem (scons x' (scons v (scons u renv))) (rename collSh (relT 0 φ)) ↔
      Sat mem (scons t (scons v (scons x' vals))) (relT 0 φ) := fun x' v u =>
    Sat_rename_ext _ _ _ _ fun n => by rcases n with _ | _ | _ | n <;> rfl
  obtain ⟨C, h1, h2⟩ := hs (fOr (fAnd (fEq 1 2) (fEq 0 3)) (fOr (fAnd (fEq 1 4) (fEq 0 4))
    (fEx (fAnd (fMem 5 0) (fAnd (singF 2 0) (fAnd (fMem 5 1)
      (rename collSh (relT 0 φ)))))))) renv r0
  have hEC : mem E C := by
    obtain ⟨z, hz, hzC⟩ := h1 E (Or.inl ⟨rfl, rfl⟩)
    rcases hz with ⟨-, hz⟩ | ⟨hz, -⟩ | ⟨x', -, hz, -⟩
    · exact (show z = E from hz) ▸ hzC
    · exact absurd hz hr0t
    · exact (hr0s x' ((sat_singF _ 2 0).mp hz)).elim
  obtain ⟨_, -, hcl⟩ := h2 E hEC
  have htC : mem t C := by
    obtain ⟨z, hz, hzC⟩ := hcl t (fun w hw => (ht w hw).elim) t (Or.inr (Or.inl ⟨rfl, rfl⟩))
    rcases hz with ⟨hz, -⟩ | ⟨-, hz⟩ | ⟨x', -, hz, -⟩
    · exact absurd hz.symm hr0t
    · exact (show z = t from hz) ▸ hzC
    · exact (hts x' ((sat_singF _ 2 0).mp hz)).elim
  refine ⟨⟨C, htC⟩, fun y hy => ?_, fun x hx ⟨y, hxy⟩ => ?_⟩
  · obtain ⟨_, hu, -⟩ := h2 y.1 hy
    rcases hu with ⟨-, hu⟩ | ⟨-, hu⟩ | ⟨x', htx', -, -, hrel⟩
    · exact (htE (by have h := y.2; rw [show y.1 = E from hu] at h; exact h)).elim
    · exact (hirr t (by have h := y.2; rw [show y.1 = t from hu] at h; exact h)).elim
    · exact ⟨⟨x', htx'⟩, (hR _ _).mpr ((hθ _ _ _).mp hrel)⟩
  · obtain ⟨sx, hsx⟩ := raw_singleton hs x.1
    have hxE : mem x.1 E := (hE x.1).mpr (Or.inr ⟨hx, x.2⟩)
    obtain ⟨z, hz, hzC⟩ := hcl sx (fun w hw => ((hsx w).mp hw) ▸ hxE) y.1
      (Or.inr (Or.inr ⟨x.1, x.2, (sat_singF _ 2 0).mpr hsx, y.2, (hθ _ _ _).mpr ((hR _ _).mp hxy)⟩))
    rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩ | ⟨x', -, hsx', htz, hrel⟩
    · exact (hr0s x.1 ((show sx = r0 from hz) ▸ hsx)).elim
    · exact (hts x.1 ((show sx = t from hz) ▸ hsx)).elim
    · have hx' : x' = x.1 := ((sat_singF _ 2 0).mp hsx').unique hsx
      subst hx'
      exact ⟨⟨z, htz⟩, hzC, (hR _ _).mpr ((hθ _ _ _).mp hrel)⟩

end TagWorld

end SetTheory.BusyBeaver.ZFC.KLower
