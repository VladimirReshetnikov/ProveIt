import BusyBeaver.ZFC.KLowerSeed

/-!
Raw set constructions in a seed model (the semantic counterpart of Elliot Glazer's `KPRaw`,
`KPPair`, `KPTransitive`, `KBase` and `KTagged`).

Each is one instance of the seed property. The root's unique image puts a first member into the
container; the closure clause, applied to the empty marker or to a singleton below a member,
pulls in the rest; and since every member is an image, nothing else gets in.

* `raw_empty`, `raw_singleton`, `raw_pair`: exact.
* `raw_transitive`: every set lies in a transitive set.
* `raw_power`: exact raw power sets.
* `raw_aug`: separation augmented by the input, `{a} ∪ {z ∈ a | θ z}`.
* `raw_tagged`: tagged comprehension `{B, t} ∪ {z ∈ B | θ z}` for the empty marker `t` and
  `B ≠ t`.

Exact separation is not available raw: the root's image is always a member.
-/

namespace SetTheory.BusyBeaver.ZFC.KLower

open SetTheory.BusyBeaver.ZFC.KSeed222 Form

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- `s = {v}`. -/
def IsSing (mem : V → V → Prop) (s v : V) : Prop := ∀ w, mem w s ↔ w = v

theorem IsSing.unique {s v v' : V} (h : IsSing mem s v) (h' : IsSing mem s v') : v = v' :=
  ((h' v).mp ((h v).mpr rfl))

/-- Inside a matrix: slot `u` is the singleton of slot `v`. -/
def singF (u v : Nat) : Form := fAll (fIff (fMem 0 (u + 1)) (fEq 0 (v + 1)))

theorem sat_singF (env : Nat → V) (u v : Nat) :
    Sat mem env (singF u v) ↔ IsSing mem (env u) (env v) :=
  forall_congr' fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Formula parameters after the matrix's own `k` parameters. -/
def shiftAfter (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => n + 2 + k

section Raw

variable (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x)
include hs

theorem raw_empty (w : V) : ∃ t, ∀ z, ¬ mem z t := by
  obtain ⟨C, -, h2⟩ := hs fBot (fun _ => w) w
  exact ⟨C, fun z hz => by obtain ⟨_, hx, -⟩ := h2 z hz; exact hx⟩

theorem raw_singleton (x : V) : ∃ s, IsSing mem s x := by
  obtain ⟨C, h1, h2⟩ := hs (fEq 0 2) (fun _ => x) x
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨_, hx, -⟩ := h2 z hz; exact hx
  · intro hzx
    obtain ⟨w, hw, hwC⟩ := h1 x rfl
    have hwx : w = x := hw
    rwa [hzx, ← hwx]

theorem raw_pair {t : V} (ht : ∀ z, ¬ mem z t) (x y : V) :
    ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y := by
  obtain ⟨A0, hA0⟩ := raw_singleton hs t
  have hA0t : A0 ≠ t := fun e => ht t (e ▸ (hA0 t).mpr rfl)
  let env : Nat → V := scons A0 (scons x (scons t (scons y (fun _ => t))))
  obtain ⟨C, h1, h2⟩ := hs (fOr (fAnd (fEq 1 2) (fEq 0 3)) (fAnd (fEq 1 4) (fEq 0 5))) env A0
  have hx : mem x C := by
    obtain ⟨z, hz, hzC⟩ := h1 x (Or.inl ⟨rfl, rfl⟩)
    rcases hz with ⟨-, hz⟩ | ⟨hz, -⟩
    · exact (show z = x from hz) ▸ hzC
    · exact absurd hz hA0t
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨_, hu, -⟩ := h2 z hz
    rcases hu with ⟨-, hu⟩ | ⟨-, hu⟩
    · exact Or.inl hu
    · exact Or.inr hu
  · rintro (rfl | rfl)
    · exact hx
    · obtain ⟨_, -, hcl⟩ := h2 x hx
      obtain ⟨z', hz', hzC⟩ := hcl t (fun w hw => (ht w hw).elim) z (Or.inr ⟨rfl, rfl⟩)
      rcases hz' with ⟨hz', -⟩ | ⟨-, hz'⟩
      · exact absurd hz'.symm hA0t
      · exact (show z' = z from hz') ▸ hzC

theorem raw_transitive (a : V) : ∃ v, mem a v ∧ ∀ y, mem y v → ∀ z, mem z y → mem z v := by
  obtain ⟨sa, hsa⟩ := raw_singleton hs a
  obtain ⟨C, h1, h2⟩ := hs (singF 1 0) (fun _ => a) sa
  have hR : ∀ x y, Sat mem (scons y (scons x (fun _ => a))) (singF 1 0) ↔ IsSing mem x y :=
    fun x y => sat_singF _ 1 0
  refine ⟨C, ?_, fun y hy z hzy => ?_⟩
  · obtain ⟨z, hz, hzC⟩ := h1 a ((hR _ _).mpr hsa)
    exact ((hsa.unique ((hR _ _).mp hz)).symm ▸ hzC : mem a C)
  · obtain ⟨_, -, hcl⟩ := h2 y hy
    obtain ⟨sz, hsz⟩ := raw_singleton hs z
    obtain ⟨z', hz', hzC⟩ := hcl sz (fun w hw => ((hsz w).mp hw) ▸ hzy) z ((hR _ _).mpr hsz)
    exact ((hsz.unique ((hR _ _).mp hz')).symm ▸ hzC : mem z C)

include hirr

theorem raw_power (a : V) : ∃ p, ∀ z, mem z p ↔ ∀ w, mem w z → mem w a := by
  obtain ⟨A0, hA0⟩ := raw_singleton hs a
  have hA0a : ¬ ∀ w, mem w A0 → mem w a := fun h => hirr a (h a ((hA0 a).mpr rfl))
  let env : Nat → V := scons A0 (scons a (fun _ => a))
  obtain ⟨C, h1, h2⟩ := hs (fOr (fAnd (fEq 1 2) (fEq 0 3))
    (fAnd (fAll (fImp (fMem 0 2) (fMem 0 4))) (fEq 0 1))) env A0
  have ha : mem a C := by
    obtain ⟨z, hz, hzC⟩ := h1 a (Or.inl ⟨rfl, rfl⟩)
    rcases hz with ⟨-, hz⟩ | ⟨hz, -⟩
    · exact (show z = a from hz) ▸ hzC
    · exact absurd hz hA0a
  refine ⟨C, fun z => ⟨fun hz => ?_, fun hsub => ?_⟩⟩
  · obtain ⟨u, hu, -⟩ := h2 z hz
    rcases hu with ⟨-, hu⟩ | ⟨hu, he⟩
    · exact (show z = a from hu) ▸ fun w hw => hw
    · exact (show z = u from he) ▸ hu
  · obtain ⟨_, -, hcl⟩ := h2 a ha
    obtain ⟨z', hz', hzC⟩ := hcl z hsub z (Or.inr ⟨hsub, rfl⟩)
    rcases hz' with ⟨hz', -⟩ | ⟨-, hz'⟩
    · exact absurd ((show z = A0 from hz') ▸ hsub) hA0a
    · exact (show z' = z from hz') ▸ hzC

theorem raw_aug (a : V) (θ : Form) (ρ : Nat → V) :
    ∃ b, ∀ z, mem z b ↔ z = a ∨ (mem z a ∧ Sat mem (scons z ρ) θ) := by
  obtain ⟨A0, hA0⟩ := raw_singleton hs a
  let env : Nat → V := scons A0 (scons a ρ)
  have hθ : ∀ x y, Sat mem (scons y (scons x env)) (rename (shiftAfter 2) θ) ↔
      Sat mem (scons y ρ) θ := fun x y =>
    Sat_rename_ext θ _ _ _ fun n => by cases n <;> rfl
  obtain ⟨C, h1, h2⟩ := hs (fOr (fAnd (fEq 1 2) (fEq 0 3))
    (fAnd (singF 1 0) (fAnd (fMem 0 3) (rename (shiftAfter 2) θ)))) env A0
  -- the root's only image is `a`
  have hroot : ∀ z, IsSing mem A0 z → mem z a → False := fun z hz hza =>
    hirr a ((hA0.unique hz) ▸ hza)
  have ha : mem a C := by
    obtain ⟨z, hz, hzC⟩ := h1 a (Or.inl ⟨rfl, rfl⟩)
    rcases hz with ⟨-, hz⟩ | ⟨hz, hza, -⟩
    · exact (show z = a from hz) ▸ hzC
    · exact (hroot z ((sat_singF _ 1 0).mp hz) hza).elim
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨_, hu, -⟩ := h2 z hz
    rcases hu with ⟨-, hu⟩ | ⟨-, hza, hθz⟩
    · exact Or.inl hu
    · exact Or.inr ⟨hza, (hθ _ _).mp hθz⟩
  · rintro (rfl | ⟨hza, hθz⟩)
    · exact ha
    · obtain ⟨_, -, hcl⟩ := h2 a ha
      obtain ⟨sz, hsz⟩ := raw_singleton hs z
      obtain ⟨z', hz', hzC⟩ := hcl sz (fun w hw => ((hsz w).mp hw) ▸ hza) z
        (Or.inr ⟨(sat_singF _ 1 0).mpr hsz, hza, (hθ _ _).mpr hθz⟩)
      rcases hz' with ⟨hz', -⟩ | ⟨hz', -⟩
      · have : z = a := hsz.unique ((show sz = A0 from hz') ▸ hA0)
        exact (hirr a (this ▸ hza)).elim
      · exact ((hsz.unique ((sat_singF _ 1 0).mp hz')).symm ▸ hzC : mem z C)

theorem raw_tagged {t : V} (ht : ∀ z, ¬ mem z t) (B : V) (hBt : B ≠ t) (θ : Form) (ρ : Nat → V) :
    ∃ S, ∀ z, mem z S ↔ z = B ∨ z = t ∨ (mem z B ∧ Sat mem (scons z ρ) θ) := by
  obtain ⟨r0, hr0⟩ := raw_pair hs ht B t
  have hr0t : r0 ≠ t := fun e => ht B (e ▸ (hr0 B).mpr (Or.inl rfl))
  have hr0s : ∀ v, ¬ IsSing mem r0 v := fun v hv =>
    hBt ((hv B).mp ((hr0 B).mpr (Or.inl rfl)) ▸ ((hv t).mp ((hr0 t).mpr (Or.inr rfl))).symm)
  have hts : ∀ v, ¬ IsSing mem t v := fun v hv => ht v ((hv v).mpr rfl)
  let env : Nat → V := scons r0 (scons B (scons t ρ))
  have hθ : ∀ x y, Sat mem (scons y (scons x env)) (rename (shiftAfter 3) θ) ↔
      Sat mem (scons y ρ) θ := fun x y =>
    Sat_rename_ext θ _ _ _ fun n => by cases n <;> rfl
  obtain ⟨C, h1, h2⟩ := hs (fOr (fAnd (fEq 1 2) (fEq 0 3)) (fOr (fAnd (fEq 1 4) (fEq 0 4))
    (fAnd (singF 1 0) (fAnd (fMem 0 3) (rename (shiftAfter 3) θ))))) env r0
  have hB : mem B C := by
    obtain ⟨z, hz, hzC⟩ := h1 B (Or.inl ⟨rfl, rfl⟩)
    rcases hz with ⟨-, hz⟩ | ⟨hz, -⟩ | ⟨hz, -⟩
    · exact (show z = B from hz) ▸ hzC
    · exact absurd hz hr0t
    · exact (hr0s z ((sat_singF _ 1 0).mp hz)).elim
  obtain ⟨_, -, hcl⟩ := h2 B hB
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨_, hu, -⟩ := h2 z hz
    rcases hu with ⟨-, hu⟩ | ⟨-, hu⟩ | ⟨-, hzB, hθz⟩
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr ⟨hzB, (hθ _ _).mp hθz⟩)
  · rintro (rfl | rfl | ⟨hzB, hθz⟩)
    · exact hB
    · obtain ⟨z', hz', hzC⟩ := hcl z (fun w hw => (ht w hw).elim) z (Or.inr (Or.inl ⟨rfl, rfl⟩))
      rcases hz' with ⟨hz', -⟩ | ⟨-, hz'⟩ | ⟨hz', -⟩
      · exact absurd hz'.symm hr0t
      · exact (show z' = z from hz') ▸ hzC
      · exact (hts z' ((sat_singF _ 1 0).mp hz')).elim
    · obtain ⟨sz, hsz⟩ := raw_singleton hs z
      obtain ⟨z', hz', hzC⟩ := hcl sz (fun w hw => ((hsz w).mp hw) ▸ hzB) z
        (Or.inr (Or.inr ⟨(sat_singF _ 1 0).mpr hsz, hzB, (hθ _ _).mpr hθz⟩))
      rcases hz' with ⟨hz', -⟩ | ⟨hz', -⟩ | ⟨hz', -⟩
      · exact (hr0s z ((show sz = r0 from hz') ▸ hsz)).elim
      · exact (hts z ((show sz = t from hz') ▸ hsz)).elim
      · exact ((hsz.unique ((sat_singF _ 1 0).mp hz')).symm ▸ hzC : mem z C)

end Raw

end SetTheory.BusyBeaver.ZFC.KLower
