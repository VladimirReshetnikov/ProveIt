import IPRADerivations.Topology.FiniteClosureMaps
import Mathlib.Data.Fintype.Card

/-!
# Necessity of the finite normality criterion and the finite Tietze extension

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, for coded (Boolean)
subsets of a finite preorder ("All subsets here have Boolean codes"), with connectedness by walks of the
comparability graph (`Topology/FiniteClosureMaps.comp`):

* F18 (`thm:finite-normal`, necessity): if disjoint closed sets have disjoint open neighbourhoods (`Normal`),
  every component has a point below all of its points (`normal_least`). The proof follows the paper:
  - every point has a minimal point below it, "with a finite bound … fewer than the number of classes
    replacements" (`exists_minimal_below`, by strong induction on the number of points below);
  - "Two distinct minimal classes `a, b` below the same `x` have disjoint closed principal ideals …
    contradicting normality" (`minimal_unique`);
  - "Following comparability paths shows that this class is constant on a component" (`walk_iff`);
* F20 (`thm:finite-tietze`): if every component has a least point (`thm:finite-normal`), a map on a closed set
  `A` that is constant on comparable points of `A` ("Comparable points of a finite domain have equal values
  under a continuous map") extends to a map constant on comparabilities, i.e. continuous (`tietze`), and any
  bound satisfied by the data and the default value holds for the extension ("If all values lie in a
  specified rational interval `[u, v]`, `F` can be chosen with the same bound").
-/

namespace LeanProofs.IPRA.Topology.FiniteNormalityConverse

open LeanProofs.IPRA.Topology.FiniteClosureMaps (comp)
open LeanProofs.IPRA.Foundations.ObservationCut.Finality (Walk)

variable {k : ℕ} {rel : Fin k → Fin k → Prop}

/-- `A` is closed (downward). -/
def Closed (rel : Fin k → Fin k → Prop) (A : Fin k → Prop) : Prop := ∀ x y, rel x y → A y → A x

/-- `U` is open (upward). -/
def Opn (rel : Fin k → Fin k → Prop) (U : Fin k → Prop) : Prop := ∀ x y, rel x y → U x → U y

/-- Normality: disjoint closed sets have disjoint open neighbourhoods. -/
def Normal (rel : Fin k → Fin k → Prop) : Prop :=
  ∀ A B : Fin k → Prop, Closed rel A → Closed rel B → (∀ z, A z → B z → False) →
    ∃ U V : Fin k → Prop, Opn rel U ∧ Opn rel V ∧ (∀ z, A z → U z) ∧ (∀ z, B z → V z) ∧
      (∀ z, U z → V z → False)

/-- `m` is minimal: everything below `m` is equivalent to `m`. -/
def Minimal (rel : Fin k → Fin k → Prop) (m : Fin k) : Prop := ∀ z, rel z m → rel m z

variable (hrefl : ∀ x, rel x x) (htrans : ∀ x y z, rel x y → rel y z → rel x z)
include hrefl htrans

/-- Every point has a minimal point below it. -/
theorem exists_minimal_below (x : Fin k) : ∃ m, rel m x ∧ Minimal rel m := by
  classical
  suffices H : ∀ N, ∀ z, (Finset.univ.filter (rel · z)).card = N → ∃ m, rel m z ∧ Minimal rel m from
    H _ x rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z hz
    by_cases hmin : Minimal rel z
    · exact ⟨z, hrefl z, hmin⟩
    · simp only [Minimal, not_forall] at hmin
      obtain ⟨w, hwz, hzw⟩ := hmin
      have hsub : Finset.univ.filter (rel · w) ⊂ Finset.univ.filter (rel · z) := by
        refine Finset.ssubset_iff_of_subset (fun v hv => ?_) |>.mpr ⟨z, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact htrans _ _ _ hv hwz
        · simp [hrefl z]
        · simp [hzw]
      obtain ⟨m, hmw, hm⟩ := ih _ (by rw [← hz]; exact Finset.card_lt_card hsub) w rfl
      exact ⟨m, htrans _ _ _ hmw hwz, hm⟩

/-- Under normality, two minimal points below a common point are comparable. -/
theorem minimal_unique (hN : Normal rel) {m m' y : Fin k} (hm : Minimal rel m) (hm' : Minimal rel m')
    (h₁ : rel m y) (h₂ : rel m' y) : rel m m' := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hAU, hBV, hdisj⟩ := hN (fun z => rel z m) (fun z => rel z m')
    (fun x y hxy hy => htrans _ _ _ hxy hy) (fun x y hxy hy => htrans _ _ _ hxy hy)
    (fun z hz hz' => hne (htrans _ _ _ (hm z hz) hz'))
  exact hdisj y (hU m y h₁ (hAU m (hrefl m))) (hV m' y h₂ (hBV m' (hrefl m')))

/-- Along a comparability walk, a minimal point lies below one end exactly when it lies below the other. -/
theorem walk_iff (hN : Normal rel) {m : Fin k} (hm : Minimal rel m) {z z' : Fin k}
    (w : Walk (comp rel) z z') : rel m z ↔ rel m z' := by
  induction w with
  | trivial => exact Iff.rfl
  | @edge a b e =>
    rcases e with e | e
    · refine ⟨fun h => htrans _ _ _ h e, fun h => ?_⟩
      obtain ⟨m'', h1, h2⟩ := exists_minimal_below hrefl htrans a
      exact htrans _ _ _ (minimal_unique hrefl htrans hN hm h2 h (htrans _ _ _ h1 e)) h1
    · refine ⟨fun h => ?_, fun h => htrans _ _ _ h e⟩
      obtain ⟨m'', h1, h2⟩ := exists_minimal_below hrefl htrans b
      exact htrans _ _ _ (minimal_unique hrefl htrans hN hm h2 h (htrans _ _ _ h1 e)) h1
  | reverse _ ih => exact ih.symm
  | join _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- F18, necessity: under normality every component has a point below all its points. -/
theorem normal_least (hN : Normal rel) (x : Fin k) : ∃ b, ∀ y, Walk (comp rel) x y → rel b y := by
  obtain ⟨m, hmx, hm⟩ := exists_minimal_below hrefl htrans x
  exact ⟨m, fun y w => (walk_iff hrefl htrans hN hm w).mp hmx⟩

omit hrefl htrans in
/-- F20: a map on a closed set, constant on its comparable points, extends to a map constant on
comparabilities, keeping every bound shared by the data and the default. -/
theorem tietze {β : Type} (hleast : ∀ x, ∃ b, ∀ y, Walk (comp rel) x y → rel b y) {A : Fin k → Prop}
    (hA : Closed rel A) (f : Fin k → β) (hf : ∀ a a', A a → A a' → rel a a' → f a = f a') (d : β) :
    ∃ F : Fin k → β, (∀ a, A a → F a = f a) ∧ (∀ x y, rel x y → F x = F y) ∧
      (∀ P : β → Prop, P d → (∀ a, A a → P (f a)) → ∀ x, P (F x)) := by
  classical
  have cons : ∀ a a', A a → A a' → Walk (comp rel) a a' → f a = f a' := by
    intro a a' ha ha' w
    obtain ⟨b, hb⟩ := hleast a
    have hba := hb a (.trivial a)
    have hba' := hb a' w
    have hAb := hA b a hba ha
    exact (hf b a hAb ha hba).symm.trans (hf b a' hAb ha' hba')
  refine ⟨fun x => if h : ∃ a, A a ∧ Walk (comp rel) a x then f h.choose else d, ?_, ?_, ?_⟩
  · intro a ha
    have h : ∃ c, A c ∧ Walk (comp rel) c a := ⟨a, ha, .trivial a⟩
    simp only [dif_pos h]
    exact cons _ _ h.choose_spec.1 ha h.choose_spec.2
  · intro x y hxy
    by_cases hx : ∃ a, A a ∧ Walk (comp rel) a x
    · have hy : ∃ a, A a ∧ Walk (comp rel) a y :=
        ⟨hx.choose, hx.choose_spec.1, .join hx.choose_spec.2 (.edge (.inl hxy))⟩
      simp only [dif_pos hx, dif_pos hy]
      exact cons _ _ hx.choose_spec.1 hy.choose_spec.1
        (.join hx.choose_spec.2 (.join (.edge (.inl hxy)) (.reverse hy.choose_spec.2)))
    · have hy : ¬ ∃ a, A a ∧ Walk (comp rel) a y := fun ⟨a, ha, w⟩ =>
        hx ⟨a, ha, .join w (.reverse (.edge (.inl hxy)))⟩
      simp only [dif_neg hx, dif_neg hy]
  · intro P hd hfA x
    by_cases hx : ∃ a, A a ∧ Walk (comp rel) a x
    · simp only [dif_pos hx]; exact hfA _ hx.choose_spec.1
    · simp only [dif_neg hx]; exact hd

end LeanProofs.IPRA.Topology.FiniteNormalityConverse
