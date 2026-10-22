import BusyBeaver.ZFC.KLowerSeed
import BusyBeaver.ZFC.KSeedFunctional

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
  obtain ⟨C, h⟩ := (seedProp_iff_closure (mem := mem)
    (fun _ _ _ hy hz => hy.trans hz.symm)).mp (hs (fEq 0 2) (fun _ => x) x)
  exact ⟨C, fun z => ⟨fun hz => (h.image z hz).elim (fun _ hx => hx), fun hz => h.root z hz⟩⟩

theorem raw_pair {t : V} (ht : ∀ z, ¬ mem z t) (x y : V) :
    ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y := by
  obtain ⟨A0, hA0⟩ := raw_singleton hs t
  have hA0t : A0 ≠ t := fun e => ht t (e ▸ (hA0 t).mpr rfl)
  let env : Nat → V := scons A0 (scons x (scons t (scons y (fun _ => t))))
  have hfun : ∀ u v w, ((u = A0 ∧ v = x) ∨ (u = t ∧ v = y)) →
      ((u = A0 ∧ w = x) ∨ (u = t ∧ w = y)) → v = w := by
    rintro u v w (⟨hu, hv⟩ | ⟨hu, hv⟩) (⟨hu', hw⟩ | ⟨hu', hw⟩)
    · exact hv.trans hw.symm
    · exact (hA0t (hu.symm.trans hu')).elim
    · exact (hA0t (hu'.symm.trans hu)).elim
    · exact hv.trans hw.symm
  obtain ⟨C, h⟩ := (seedProp_iff_closure hfun).mp
    (hs (fOr (fAnd (fEq 1 2) (fEq 0 3)) (fAnd (fEq 1 4) (fEq 0 5))) env A0)
  have hx := h.root x (Or.inl ⟨rfl, rfl⟩)
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · exact (h.image z hz).elim fun _ hu => hu.imp And.right And.right
  · rintro (rfl | rfl)
    · exact hx
    · exact h.step x hx t (fun w hw => (ht w hw).elim) z (Or.inr ⟨rfl, rfl⟩)

theorem raw_transitive (a : V) : ∃ v, mem a v ∧ ∀ y, mem y v → ∀ z, mem z y → mem z v := by
  obtain ⟨sa, hsa⟩ := raw_singleton hs a
  have hR : ∀ x y, Sat mem (scons y (scons x (fun _ => a))) (singF 1 0) ↔ IsSing mem x y :=
    fun x y => sat_singF _ 1 0
  obtain ⟨C, h⟩ := (seedProp_iff_closure (fun x y z hy hz =>
    ((hR x y).mp hy).unique ((hR x z).mp hz))).mp (hs (singF 1 0) (fun _ => a) sa)
  refine ⟨C, h.root a ((hR sa a).mpr hsa), fun y hy z hzy => ?_⟩
  obtain ⟨sz, hsz⟩ := raw_singleton hs z
  exact h.step y hy sz (fun w hw => ((hsz w).mp hw) ▸ hzy) z ((hR sz z).mpr hsz)

include hirr

theorem raw_power (a : V) : ∃ p, ∀ z, mem z p ↔ ∀ w, mem w z → mem w a := by
  obtain ⟨A0, hA0⟩ := raw_singleton hs a
  have hA0a : ¬ ∀ w, mem w A0 → mem w a := fun h => hirr a (h a ((hA0 a).mpr rfl))
  let env : Nat → V := scons A0 (scons a (fun _ => a))
  have hfun : ∀ u v w, ((u = A0 ∧ v = a) ∨ ((∀ z, mem z u → mem z a) ∧ v = u)) →
      ((u = A0 ∧ w = a) ∨ ((∀ z, mem z u → mem z a) ∧ w = u)) → v = w := by
    rintro u v w (⟨hu, hv⟩ | ⟨hu, hv⟩) (⟨hu', hw⟩ | ⟨hu', hw⟩)
    · exact hv.trans hw.symm
    · exact (hA0a (hu ▸ hu')).elim
    · exact (hA0a (hu' ▸ hu)).elim
    · exact hv.trans hw.symm
  obtain ⟨C, h⟩ := (seedProp_iff_closure hfun).mp (hs (fOr (fAnd (fEq 1 2) (fEq 0 3))
    (fAnd (fAll (fImp (fMem 0 2) (fMem 0 4))) (fEq 0 1))) env A0)
  have ha := h.root a (Or.inl ⟨rfl, rfl⟩)
  refine ⟨C, fun z => ⟨fun hz => ?_, fun hsub => ?_⟩⟩
  · obtain ⟨u, hu⟩ := h.image z hz
    rcases hu with ⟨-, hu⟩ | ⟨hu, he⟩
    · exact (show z = a from hu) ▸ fun w hw => hw
    · exact (show z = u from he) ▸ hu
  · exact h.step a ha z hsub z (Or.inr ⟨hsub, rfl⟩)

omit hirr in
/-- Augmented separation needs no irreflexivity: overlapping root/singleton
branches still have the same unique output. -/
theorem raw_aug_core (a : V) (θ : Form) (ρ : Nat → V) :
    ∃ b, ∀ z, mem z b ↔ z = a ∨ (mem z a ∧ Sat mem (scons z ρ) θ) := by
  obtain ⟨A0, hA0⟩ := raw_singleton hs a
  let env : Nat → V := scons A0 (scons a ρ)
  have hθ : ∀ x y, Sat mem (scons y (scons x env)) (rename (shiftAfter 2) θ) ↔
      Sat mem (scons y ρ) θ := fun x y =>
    Sat_rename_ext θ _ _ _ fun n => by cases n <;> rfl
  let φ := fOr (fAnd (fEq 1 2) (fEq 0 3))
    (fAnd (singF 1 0) (fAnd (fMem 0 3) (rename (shiftAfter 2) θ)))
  have hfun : ∀ u v w, Sat mem (scons v (scons u env)) φ →
      Sat mem (scons w (scons u env)) φ → v = w := by
    rintro u v w (⟨hu, hv⟩ | ⟨hv, -⟩) (⟨hu', hw⟩ | ⟨hw, -⟩)
    · exact hv.trans hw.symm
    · exact hv.trans (hA0.unique ((show u = A0 from hu) ▸ (sat_singF _ 1 0).mp hw))
    · exact (((sat_singF _ 1 0).mp hv).unique (hu'.symm ▸ hA0)).trans hw.symm
    · exact ((sat_singF _ 1 0).mp hv).unique ((sat_singF _ 1 0).mp hw)
  obtain ⟨C, h⟩ := (seedProp_iff_closure hfun).mp (hs φ env A0)
  have ha := h.root a (Or.inl ⟨rfl, rfl⟩)
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨_, hu⟩ := h.image z hz
    rcases hu with ⟨-, hu⟩ | ⟨-, hza, hθz⟩
    · exact Or.inl hu
    · exact Or.inr ⟨hza, (hθ _ _).mp hθz⟩
  · rintro (rfl | ⟨hza, hθz⟩)
    · exact ha
    · obtain ⟨sz, hsz⟩ := raw_singleton hs z
      exact h.step a ha sz (fun w hw => ((hsz w).mp hw) ▸ hza) z
        (Or.inr ⟨(sat_singF _ 1 0).mpr hsz, hza, (hθ _ _).mpr hθz⟩)

/-- Compatibility with the maintained public signature. -/
theorem raw_aug (a : V) (θ : Form) (ρ : Nat → V) :
    ∃ b, ∀ z, mem z b ↔ z = a ∨ (mem z a ∧ Sat mem (scons z ρ) θ) :=
  raw_aug_core hs a θ ρ

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
  let φ := fOr (fAnd (fEq 1 2) (fEq 0 3)) (fOr (fAnd (fEq 1 4) (fEq 0 4))
    (fAnd (singF 1 0) (fAnd (fMem 0 3) (rename (shiftAfter 3) θ))))
  have hfun : ∀ u v w, Sat mem (scons v (scons u env)) φ →
      Sat mem (scons w (scons u env)) φ → v = w := by
    rintro u v w (⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hv, -⟩)
      (⟨hu', hw⟩ | ⟨hu', hw⟩ | ⟨hw, -⟩)
    · exact hv.trans hw.symm
    · exact (hr0t (hu.symm.trans hu')).elim
    · exact (hr0s w ((show u = r0 from hu) ▸ (sat_singF _ 1 0).mp hw)).elim
    · exact (hr0t (hu'.symm.trans hu)).elim
    · exact hv.trans hw.symm
    · exact (hts w ((show u = t from hu) ▸ (sat_singF _ 1 0).mp hw)).elim
    · exact (hr0s v ((show u = r0 from hu') ▸ (sat_singF _ 1 0).mp hv)).elim
    · exact (hts v ((show u = t from hu') ▸ (sat_singF _ 1 0).mp hv)).elim
    · exact ((sat_singF _ 1 0).mp hv).unique ((sat_singF _ 1 0).mp hw)
  obtain ⟨C, h⟩ := (seedProp_iff_closure hfun).mp (hs φ env r0)
  have hB := h.root B (Or.inl ⟨rfl, rfl⟩)
  refine ⟨C, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨_, hu⟩ := h.image z hz
    rcases hu with ⟨-, hu⟩ | ⟨-, hu⟩ | ⟨-, hzB, hθz⟩
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr ⟨hzB, (hθ _ _).mp hθz⟩)
  · rintro (rfl | rfl | ⟨hzB, hθz⟩)
    · exact hB
    · exact h.step B hB z (fun w hw => (ht w hw).elim) z (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain ⟨sz, hsz⟩ := raw_singleton hs z
      exact h.step B hB sz (fun w hw => ((hsz w).mp hw) ▸ hzB) z
        (Or.inr (Or.inr ⟨(sat_singF _ 1 0).mpr hsz, hzB, (hθ _ _).mpr hθz⟩))

end Raw

end SetTheory.BusyBeaver.ZFC.KLower
