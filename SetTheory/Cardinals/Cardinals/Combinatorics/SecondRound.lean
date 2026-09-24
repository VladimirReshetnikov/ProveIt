/-
  Combinatorial cores of the second round of reports (synthesis §12).

  * `isCyclic_map_snd` — the cyclic-stabilizer lemma (synthesis Lemma 12.11, report R13):
    a subgroup of `ℤ × Γ` whose projection to `ℤ` is injective has cyclic image in `Γ`.
    Here the subgroup is `G_w = {(d, g) : w(n + d) = g • w(n) eventually}` and its image is
    the stabilizer of the shift-tail class of the incidence word `w`.
  * `eq_univ_of_image_succ_eq` — full phase spectrum (synthesis Theorem 12.7, report R12):
    a nonempty set of integers invariant under `r ↦ r + 1` is all of `ℤ`.
  * `two_sided_orbit_lt_crit` — no nonconstant two-sided ordinal orbit (report R12).
  * `fixed_small_set_below_crit` — fixed small sets of ordinals lie below the critical
    point (synthesis Lemma 8.4(a)), from `OrdinalLemmas.strictMonoOn_image_eq_self`.

  Nothing is admitted in this file.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Cardinals.Combinatorics.Ordinals

universe u

namespace Cardinals.SecondRound

/-! ### Cyclic stabilizers -/

/-- **Cyclic stabilizers (synthesis Lemma 12.11).**  If `H ≤ ℤ × Γ` meets `{0} × Γ`
trivially, then the projection of `H` to `Γ` is cyclic. -/
theorem isCyclic_map_snd {Γ : Type*} [Group Γ] (H : Subgroup (Multiplicative ℤ × Γ))
    (hinj : ∀ x ∈ H, x.1 = 1 → x.2 = 1) :
    IsCyclic (H.map (MonoidHom.snd (Multiplicative ℤ) Γ)) := by
  -- `H` embeds into `ℤ`
  let f : H →* Multiplicative ℤ := (MonoidHom.fst (Multiplicative ℤ) Γ).comp H.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x.1.1 = 1 := hx
    have h2 : x.1.2 = 1 := hinj x.1 x.2 h1
    exact Subtype.ext (Prod.ext h1 h2)
  haveI : IsCyclic H := isCyclic_of_injective f hf
  -- and surjects onto its projection
  let g : H →* H.map (MonoidHom.snd (Multiplicative ℤ) Γ) :=
    ((MonoidHom.snd (Multiplicative ℤ) Γ).comp H.subtype).codRestrict _
      (fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective g hg

/-! ### Full integer phase -/

/-- **Full phase spectrum (synthesis Theorem 12.7).**  The spectrum of a fixed fibre
satisfies `Spec = Spec + 1`; being nonempty, it is all of `ℤ`. -/
theorem eq_univ_of_image_succ_eq (S : Set ℤ) (hne : S.Nonempty)
    (hS : (fun r => r + 1) '' S = S) : S = Set.univ := by
  obtain ⟨r₀, hr₀⟩ := hne
  have hup : ∀ r ∈ S, r + 1 ∈ S := fun r hr => hS ▸ Set.mem_image_of_mem _ hr
  have hdown : ∀ r ∈ S, r - 1 ∈ S := by
    intro r hr
    rw [← hS] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    simpa using ht
  have hnat_up : ∀ n : ℕ, r₀ + n ∈ S := by
    intro n
    induction n with
    | zero => simpa using hr₀
    | succ n ih =>
      have := hup _ ih
      simpa [add_assoc] using this
  have hnat_down : ∀ n : ℕ, r₀ - n ∈ S := by
    intro n
    induction n with
    | zero => simpa using hr₀
    | succ n ih =>
      have := hdown _ ih
      simpa [sub_sub] using this
  ext r
  simp only [Set.mem_univ, iff_true]
  rcases le_total r₀ r with h | h
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
    have := hnat_up n
    rwa [← hn, add_sub_cancel] at this
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
    have := hnat_down n
    rwa [← hn, sub_sub_cancel] at this

/-! ### Two-sided ordinal orbits -/

/-- **No nonconstant two-sided ordinal orbit (report R12).**  If `e` fixes the ordinals
below `κ`, moves those of `[κ, lam)` upward, and `e (θ (r + 1)) = θ r` for a two-sided
sequence of ordinals below `lam`, then every `θ r` is below `κ` (and hence the sequence is
constant). -/
theorem two_sided_orbit_lt_crit (e : Ordinal.{u} → Ordinal.{u}) (lam κ : Ordinal.{u})
    (hfix : ∀ ξ < κ, e ξ = ξ) (hmove : ∀ ξ, κ ≤ ξ → ξ < lam → ξ < e ξ)
    (θ : ℤ → Ordinal.{u}) (hlt : ∀ r, θ r < lam) (hθ : ∀ r, e (θ (r + 1)) = θ r) :
    ∀ r, θ r < κ := by
  -- strong induction on the value `θ r`
  have key : ∀ o : Ordinal.{u}, ∀ r, θ r = o → κ ≤ o → False := by
    intro o
    induction o using WellFoundedLT.induction with
    | ind o ih =>
      intro r hr hκ
      have hnext : κ ≤ θ (r + 1) := by
        by_contra hlt'
        rw [not_le] at hlt'
        have := hθ r
        rw [hfix _ hlt'] at this
        rw [← hr, ← this] at hκ
        exact absurd hlt' (not_lt.mpr hκ)
      have hdesc : θ (r + 1) < o := by
        have := hmove _ hnext (hlt (r + 1))
        rwa [hθ r, hr] at this
      exact ih (θ (r + 1)) hdesc (r + 1) rfl hnext
  intro r
  by_contra hge
  exact key (θ r) r rfl (not_lt.mp hge)

theorem two_sided_orbit_const (e : Ordinal.{u} → Ordinal.{u}) (lam κ : Ordinal.{u})
    (hfix : ∀ ξ < κ, e ξ = ξ) (hmove : ∀ ξ, κ ≤ ξ → ξ < lam → ξ < e ξ)
    (θ : ℤ → Ordinal.{u}) (hlt : ∀ r, θ r < lam) (hθ : ∀ r, e (θ (r + 1)) = θ r) :
    ∀ r, θ (r + 1) = θ r := by
  intro r
  have h := two_sided_orbit_lt_crit e lam κ hfix hmove θ hlt hθ (r + 1)
  rw [← hθ r, hfix _ h]

/-! ### Fixed small sets of ordinals -/

/-- **Fixed small sets lie below the critical point (synthesis Lemma 8.4(a)).**  If `e` is
strictly increasing on `lam`, moves `[κ, lam)` upward, and maps `S ⊆ lam` onto itself,
then `S ⊆ κ`.  (For `|S| < lam` the hypothesis `e '' S = S` follows from `j(S) = S`.) -/
theorem fixed_small_set_below_crit (e : Ordinal.{u} → Ordinal.{u}) (lam κ : Ordinal.{u})
    (hmono : ∀ a b, a < b → b < lam → e a < e b)
    (hmove : ∀ ξ, κ ≤ ξ → ξ < lam → ξ < e ξ)
    (S : Set Ordinal.{u}) (hS : ∀ x ∈ S, x < lam) (himage : e '' S = S) :
    ∀ x ∈ S, x < κ := by
  have hid := OrdinalLemmas.strictMonoOn_image_eq_self e S
    (fun x _ y hy hxy => hmono x y hxy (hS y hy)) himage
  intro x hx
  by_contra hge
  have := hmove x (not_lt.mp hge) (hS x hx)
  rw [hid x hx] at this
  exact lt_irrefl _ this

end Cardinals.SecondRound
