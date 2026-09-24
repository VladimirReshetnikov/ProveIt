/-
  MACHINERY FOR THE CONSTRUCTIBLE UNIVERSE
  (research note "Exacting embeddings of countable structures", Theorems 4.1 and 6.1).

  Neither Mathlib nor ProveIt has the constructible hierarchy, so the statements of
  Theorems 4.1 and 6.1 could not even be written down in the earlier files.  This file
  supplies the missing layer as an *interface*: a structure whose fields are exactly the
  published facts about `L`, the Silver indiscernibles and the least stable ordinal that
  the note's proofs use.  Each field carries its citation.  Theorems 4.1(1),(2) and
  6.1(2),(4) are then *derived* from the interface; 6.1(1) needs one further published
  input (Shoenfield absoluteness), admitted as a theorem.

  Assuming `SilverData` is assuming `0^#`: by Silver's theorem the two are equivalent, and
  we take the machinery itself as the hypothesis rather than introducing an opaque constant
  for `0^#`.  All witnesses here carry the empty predicate.

  Contents:
  * `SilverData`   -- the levels of `L`, the indiscernibles, the shift embeddings;
  * `SilverData.witness` -- the assembled `TWitness`, with `crit = i_m` and cofinal type
    (note, Theorem 4.1(1),(2));
  * `StableData`   -- the least stable ordinal and `Σ₁`-reflection to it;
  * `least_LExacting_lt_stable`, `LExacting_of_silver` (note, Theorem 6.1(2),(4));
  * `HasGraphIn`, `Published.lExacting_absolute` (note, Theorem 6.1(1)).
-/
import Cardinals.Virtual.Regularity

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal FirstOrder FirstOrder.Language
open SetTheory (Form Sat scons)
open SetTheory.Form

/-! ### The interface -/

/-- **The constructible hierarchy with Silver indiscernibles.**

Every field is a published fact; the citations are, throughout,
T. Jech, *Set Theory*, 3rd millennium ed., Springer 2003, Chapters 13 and 18, and
A. Kanamori, *The Higher Infinite*, 2nd ed., Springer 2003, §3 and §9.

* `lev`, `lev_trans`, `lev_mono`, `lev_ord`: the levels `L_α` of the constructible
  hierarchy are transitive, increasing, and `L_α ∩ Ord = α` [Jech, Lemma 13.1 and
  Theorem 13.2].
* `ind`, `ind_mono`, `ind_sup_omega`: if `0^#` exists there is a closed unbounded class of
  Silver indiscernibles for `L`; `ind` is its increasing enumeration, so it is continuous
  and `ind ω = sup_n (ind n)` [Jech, Theorem 18.20; Kanamori, Theorem 9.17].
* `Good`, `good_*`: the heights at which the machinery is applied.  Unboundedly many
  levels satisfy ZFC when `0^#` exists, since every indiscernible `i_α` has
  `L_{i_α} ≺ L` [Jech, Lemma 18.25].
* `hull`, `incl`, `shift` and their equations: Silver's theorem that an order-preserving
  map of the indiscernibles induces an elementary embedding of the Skolem hull they
  generate.  `hull m ζ` is (the trace on `L_ζ` of) the hull of the indiscernibles, `incl`
  its inclusion, and `shift m ζ` the embedding induced by the map that sends `i_n` to
  `i_{n+1}` for `n ≥ m` and fixes every other indiscernible [Jech, Lemmas 18.22-18.24 and
  Theorem 18.20; Kanamori, §9, the proof of Theorem 9.17].
* `base`: every element of `L_ζ` of rank below `i_ω` lies in the hull, because its value
  is a Skolem term in indiscernibles below `i_ω` and does not depend on the larger ones
  [Jech, Lemma 18.23].
* `shift_fixes_below`: the induced embedding fixes every ordinal below `i_m`, so its
  critical point is `i_m` [Jech, Theorem 18.20]. -/
structure SilverData where
  /-- the levels `L_α` -/
  lev : Ordinal.{u} → ZFSet.{u}
  lev_trans : ∀ α, (lev α).IsTransitive
  lev_mono : ∀ {α β : Ordinal.{u}}, α ≤ β → lev α ⊆ lev β
  lev_ord : ∀ {ξ α : Ordinal.{u}}, ξ < α → ordZ ξ ∈ lev α
  /-- the increasing enumeration of the Silver indiscernibles -/
  ind : Ordinal.{u} → Ordinal.{u}
  ind_mono : StrictMono ind
  ind_sup_omega : ∀ ξ < ind ω, ∃ n : ℕ, ξ < ind n
  /-- the heights at which the hulls are taken -/
  Good : Ordinal.{u} → Prop
  good_gt : ∀ {ζ}, Good ζ → ind ω < ζ
  good_lim : ∀ {ζ}, Good ζ → ∀ a < ζ, a + 1 < ζ
  good_zfc : ∀ {ζ}, Good ζ → IsSetModelZFC (lev ζ)
  good_unbounded : ∀ α : Ordinal.{u}, ∃ ζ, Good ζ ∧ α < ζ
  /-- the Skolem hull of the indiscernibles, traced on `L_ζ` -/
  hull : ℕ → Ordinal.{u} → ZFSet.{u}
  hull_sub : ∀ m ζ, hull m ζ ⊆ lev ζ
  incl : ∀ m ζ, Str (hull m ζ) (∅ : ZFSet.{u}) ↪ₑ[Lex] Str (lev ζ) (∅ : ZFSet.{u})
  incl_val : ∀ m ζ (x : Str (hull m ζ) (∅ : ZFSet.{u})), ((incl m ζ) x).1 = x.1
  /-- the embedding induced by shifting `i_n ↦ i_{n+1}` for `n ≥ m` -/
  shift : ∀ m ζ, Str (hull m ζ) (∅ : ZFSet.{u}) ↪ₑ[Lex] Str (lev ζ) (∅ : ZFSet.{u})
  /-- everything of rank below `i_ω` is in the hull -/
  base : ∀ m ζ, Good ζ → ∀ x, x ∈ lev ζ → x ∈ V_ (ind ω) → x ∈ hull m ζ
  /-- the indiscernibles below `ζ` are in the hull -/
  ind_mem_hull : ∀ m ζ (α : Ordinal.{u}), Good ζ → ind α < ζ → ordZ (ind α) ∈ hull m ζ
  /-- the shift fixes `i_ω` -/
  shift_ind_omega : ∀ m ζ (hζ : Good ζ),
    ((shift m ζ) ⟨ordZ (ind ω), ind_mem_hull m ζ ω hζ (good_gt hζ)⟩).1 = ordZ (ind ω)
  /-- the shift fixes every ordinal below `i_m` -/
  shift_fixes_below : ∀ m ζ (ξ : Ordinal.{u}) (h : ordZ ξ ∈ hull m ζ), ξ < ind m →
    ((shift m ζ) ⟨ordZ ξ, h⟩).1 = ordZ ξ
  /-- the shift sends `i_n` to `i_{n+1}` for `n ≥ m` -/
  shift_ind_ge : ∀ m ζ (n : ℕ) (h : ordZ (ind n) ∈ hull m ζ), m ≤ n →
    ((shift m ζ) ⟨ordZ (ind n), h⟩).1 = ordZ (ind (n + 1))

namespace SilverData

variable (S : SilverData.{u})

theorem ind_lt_omega_lt {n : ℕ} : S.ind n < S.ind ω :=
  S.ind_mono (Ordinal.natCast_lt_omega0 n)

theorem ind_lt_good {ζ : Ordinal.{u}} (hζ : S.Good ζ) {n : ℕ} : S.ind n < ζ :=
  (S.ind_lt_omega_lt).trans (S.good_gt hζ)

theorem ind_omega_limit : ∀ a < S.ind ω, a + 1 < S.ind ω := by
  intro a ha
  obtain ⟨n, hn⟩ := S.ind_sup_omega a ha
  exact (Order.add_one_le_of_lt hn).trans_lt S.ind_lt_omega_lt

/-- **The witness of Theorem 4.1.**  For every good height `ζ` and every `m`, the shift of
the indiscernibles above `i_m` is an exacting witness at `i_ω` over `L_ζ`. -/
noncomputable def witness (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ) :
    TWitness (S.lev ζ) (S.ind ω) (∅ : ZFSet.{u}) where
  X := S.hull m ζ
  X_sub := S.hull_sub m ζ
  trans := S.lev_trans ζ
  incl := S.incl m ζ
  incl_val := S.incl_val m ζ
  j := S.shift m ζ
  base := S.base m ζ hζ
  lam_mem := S.ind_mem_hull m ζ ω hζ (S.good_gt hζ)
  j_lam := S.shift_ind_omega m ζ hζ
  moves := by
    refine ⟨S.ind m, S.ind_lt_omega_lt, S.ind_mem_hull m ζ m hζ (S.ind_lt_good hζ), ?_⟩
    rw [S.shift_ind_ge m ζ m _ le_rfl]
    intro h
    exact absurd (ordZ_inj h) (ne_of_gt (S.ind_mono (by exact_mod_cast Nat.lt_succ_self m)))

theorem witness_jOrd_ind (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ) {n : ℕ} (hn : m ≤ n) :
    (S.witness m ζ hζ).jOrd (S.ind n) = S.ind (n + 1) := by
  have hlt : S.ind n < S.ind ω := S.ind_lt_omega_lt
  have h := (S.witness m ζ hζ).jv_ordX hlt
  have h2 : (S.witness m ζ hζ).jv ((S.witness m ζ hζ).ordX (S.ind n) hlt) =
      ordZ (S.ind (n + 1)) := S.shift_ind_ge m ζ n _ hn
  rw [h] at h2
  exact ordZ_inj h2

theorem witness_jOrd_below (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ) {ξ : Ordinal.{u}}
    (hξ : ξ < S.ind m) : (S.witness m ζ hζ).jOrd ξ = ξ := by
  have hlt : ξ < S.ind ω := hξ.trans S.ind_lt_omega_lt
  have h := (S.witness m ζ hζ).jv_ordX hlt
  have h2 : (S.witness m ζ hζ).jv ((S.witness m ζ hζ).ordX ξ hlt) = ordZ ξ :=
    S.shift_fixes_below m ζ ξ _ hξ
  rw [h] at h2
  exact ordZ_inj h2

/-- The critical point of the witness is `i_m`. -/
theorem witness_crit (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ) :
    (S.witness m ζ hζ).crit = S.ind m := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    have hlt : S.ind m < (S.witness m ζ hζ).crit := not_le.mp hcon
    have hfix := (S.witness m ζ hζ).jOrd_of_lt_crit hlt
    rw [S.witness_jOrd_ind m ζ hζ (le_refl m)] at hfix
    exact absurd hfix (ne_of_gt (S.ind_mono (by exact_mod_cast Nat.lt_succ_self m)))
  · by_contra hcon
    have hlt : (S.witness m ζ hζ).crit < S.ind m := not_le.mp hcon
    exact (S.witness m ζ hζ).jOrd_crit_ne (S.witness_jOrd_below m ζ hζ hlt)

/-- The critical sequence of the witness is `i_m, i_{m+1}, …`. -/
theorem witness_critSeq (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ) (n : ℕ) :
    (S.witness m ζ hζ).critSeq n = S.ind (((m + n : ℕ) : Ordinal.{u})) := by
  induction n with
  | zero =>
    have h0 : (S.witness m ζ hζ).critSeq 0 = (S.witness m ζ hζ).crit := rfl
    rw [h0, S.witness_crit m ζ hζ]
    simp
  | succ n ih =>
    rw [TWitness.critSeq_succ, ih, S.witness_jOrd_ind m ζ hζ (Nat.le_add_right m n)]
    congr 1

/-- **Theorem 4.1(1).**  The witness is of cofinal type: its critical sequence is cofinal
in `i_ω`. -/
theorem witness_cofinalType (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ) :
    (S.witness m ζ hζ).CofinalType := by
  intro ξ hξ
  obtain ⟨n, hn⟩ := S.ind_sup_omega ξ hξ
  refine ⟨n, ?_⟩
  rw [S.witness_critSeq m ζ hζ n]
  exact hn.trans_le (S.ind_mono.monotone (by exact_mod_cast Nat.le_add_left n m))

/-- **Theorem 4.1(1), final form.**  `i_ω` carries exacting witnesses of cofinal type over
`L_ζ` for unboundedly many `ζ`, and with critical point above any prescribed `i_m`. -/
theorem virtually_exacting_cofinal (α : Ordinal.{u}) (m : ℕ) :
    ∃ ζ, S.Good ζ ∧ α < ζ ∧ ∃ w : TWitness (S.lev ζ) (S.ind ω) (∅ : ZFSet.{u}),
      w.CofinalType ∧ w.crit = S.ind m := by
  obtain ⟨ζ, hζ, hα⟩ := S.good_unbounded α
  exact ⟨ζ, hζ, hα, S.witness m ζ hζ, S.witness_cofinalType m ζ hζ, S.witness_crit m ζ hζ⟩

/-- `i_ω` satisfies the hypothesis `HasHighWitnesses` of `Virtual/Regularity.lean`: for
every `α < i_ω` there is a witness of cofinal type with critical point above `α`. -/
theorem hasHighWitnesses (ζ : Ordinal.{u}) (hζ : S.Good ζ) :
    HasHighWitnesses (S.lev ζ) (S.ind ω) (∅ : ZFSet.{u}) := by
  intro α hα
  obtain ⟨n, hn⟩ := S.ind_sup_omega α hα
  exact ⟨S.witness n ζ hζ, S.witness_cofinalType n ζ hζ,
    by rw [S.witness_crit n ζ hζ]; exact hn⟩

/-- **Theorem 4.1(3), mathematical content.**  The conclusions of Theorem 3.1 -- in
particular the inaccessibility of every `κ_n` in `L_ζ` -- hold at `i_ω` inside `L`, where
`λ` is *not* singular and `V = HOD`.  The consistency statement itself is metamathematical
and is not formalized. -/
theorem crit_inaccessible_in_L (m : ℕ) (ζ : Ordinal.{u}) (hζ : S.Good ζ)
    (hP : PairClosed (S.lev ζ)) (hpow : ∀ y ∈ S.lev ζ, powA (S.lev ζ) y ∈ S.lev ζ)
    (n : ℕ) : SLSemA (S.lev ζ) (ordZ (S.ind (((m + n : ℕ) : Ordinal.{u})))) := by
  have := (S.witness m ζ hζ).slSem_critSeq hP hpow S.ind_omega_limit n
  rwa [S.witness_critSeq m ζ hζ n] at this

/-- **Theorem 5.1(3) inside `L`.**  At `i_ω`, over a good level of `L`, no short cofinal
subset of `i_ω` is definable from parameters of rank below `i_ω`.  This combines the
machinery of this file with `no_short_cofinal_low_rank`: the required
`HasHighWitnesses` hypothesis is supplied by the indiscernibles. -/
theorem no_short_cofinal_in_L (ζ : Ordinal.{u}) (hζ : S.Good ζ) (hP : PairClosed (S.lev ζ))
    (φ : Form) (ps : ℕ → ZFSet.{u}) (ρ : Ordinal.{u}) (hρ : ρ < S.ind ω)
    (hpsA : ∀ n, ps n ∈ S.lev ζ) (hpsV : ∀ n, ps n ∈ V_ ρ ∨ ps n = ordZ (S.ind ω))
    (a : ZFSet.{u}) (haA : a ∈ S.lev ζ)
    (hdef : ∀ y : Carrier (S.lev ζ),
      Sat (memOn (S.lev ζ)) (scons y (fun n => (⟨ps n, hpsA n⟩ : Carrier (S.lev ζ)))) φ ↔
        y.1 = a)
    (hcof : CofinalIn a (S.ind ω))
    (hsmall : ∃ μ, μ < S.ind ω ∧ ∃ f ∈ S.lev ζ, SurjSem (S.lev ζ) f (ordZ μ) a) : False :=
  no_short_cofinal_low_rank (S.good_zfc hζ).toZF hP (S.hasHighWitnesses ζ hζ)
    φ ps ρ hρ hpsA hpsV a haA hdef hcof hsmall

end SilverData

/-! ### The least stable ordinal -/

/-- `w` has its graph in the set `S` (so the witness is an object of `L` when `S` is a
level of `L`). -/
def TWitness.HasGraphIn {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}}
    (w : TWitness A lam Y) (S : ZFSet.{u}) : Prop :=
  w.X ∈ S ∧ ∃ g ∈ S, ∀ p, p ∈ g ↔ ∃ x : Str w.X Y, p = pair x.1 (w.jv x)

/-- `lam` is *`L`-exacting* with respect to `S`: some good level of `L` carries a witness
at `lam`.  (Note, Definition 2.2.) -/
def LExacting (S : SilverData.{u}) (lam : Ordinal.{u}) : Prop :=
  ∃ ζ, S.Good ζ ∧ Nonempty (TWitness (S.lev ζ) lam (∅ : ZFSet.{u}))

/-- **The least stable ordinal and `Σ₁`-reflection to it.**

`stable` is the least `σ` with `L_σ ≺_{Σ₁} L`.  The field `stable_reflect` is the instance
of `Σ₁`-reflection used in the note: "some ordinal is `L`-exacting" is `Σ₁` over `L` (it
asserts the existence of a level, a hull and an embedding), so if it holds it holds below
`σ`.  `stable_countable` is the standard fact that `σ` is countable, by Löwenheim-Skolem
and condensation.

Reference: K. Devlin, *Constructibility*, Springer 1984, Chapter II (the `Σ₁`-projectum and
stable ordinals); T. Jech, *Set Theory*, 3rd millennium ed., Lemma 13.10 (condensation) and
Chapter 25; G. E. Sacks, *Higher Recursion Theory*, Springer 1990, Chapter II §5 (the least
stable ordinal `σ` satisfies `L_σ ≺_{Σ₁} L` and is countable). -/
structure StableData (S : SilverData.{u}) where
  stable : Ordinal.{u}
  stable_countable : stable.card ≤ ℵ₀
  stable_reflect : (∃ lam, LExacting S lam) → ∃ lam < stable, LExacting S lam
  stable_reflect_at : ∀ lam < stable, LExacting S lam →
    ∃ ζ < stable, S.Good ζ ∧ Nonempty (TWitness (S.lev ζ) lam (∅ : ZFSet.{u}))

namespace StableData

variable {S : SilverData.{u}} (D : StableData S)

/-- **Theorem 6.1(2).**  If any ordinal is `L`-exacting, the least one lies below the least
stable ordinal, and a witness for it lives below the least stable ordinal too. -/
theorem least_LExacting_lt_stable (h : ∃ lam, LExacting S lam) :
    ∃ lam, LExacting S lam ∧ lam < D.stable ∧ (∀ μ < lam, ¬ LExacting S μ) ∧
      ∃ ζ < D.stable, S.Good ζ ∧ Nonempty (TWitness (S.lev ζ) lam (∅ : ZFSet.{u})) := by
  classical
  obtain ⟨lam₀, hlam₀⟩ := h
  let P : Set Ordinal.{u} := {lam | LExacting S lam}
  have hPne : P.Nonempty := ⟨lam₀, hlam₀⟩
  let lam := wellFounded_lt.min P hPne
  have hlam : LExacting S lam := wellFounded_lt.min_mem P hPne
  have hmin : ∀ μ < lam, ¬ LExacting S μ := fun μ hμ hμP =>
    wellFounded_lt.not_lt_min P hμP hμ
  -- reflection produces an `L`-exacting ordinal below `stable`, so the least one is below
  obtain ⟨lam', hlam'st, hlam'⟩ := D.stable_reflect ⟨lam₀, hlam₀⟩
  have hlamle : lam ≤ lam' := by
    by_contra hcon
    exact hmin lam' (not_le.mp hcon) hlam'
  have hlamst : lam < D.stable := hlamle.trans_lt hlam'st
  exact ⟨lam, hlam, hlamst, hmin, D.stable_reflect_at lam hlamst hlam⟩

end StableData

/-- **Theorem 6.1(4).**  If `0^#` exists -- that is, if the Silver machinery is available --
then `L`-exacting ordinals exist, with witnesses of cofinal type. -/
theorem LExacting_of_silver (S : SilverData.{u}) : ∃ lam, LExacting S lam := by
  obtain ⟨ζ, hζ, -⟩ := S.good_unbounded 0
  exact ⟨S.ind ω, ζ, hζ, ⟨S.witness 0 ζ hζ⟩⟩

namespace Published

/-- **Theorem 6.1(1): Shoenfield absoluteness.**  "Some countable ordinal is `L`-exacting"
is a `Σ¹₂` statement -- it asserts the existence of a real coding a countable level `L_ζ`
together with a hull and an embedding -- so it is absolute between `V` and `L`; and a
witness may then be taken inside `L`.

Reference: T. Jech, *Set Theory*, 3rd millennium ed., Springer 2003, Theorem 25.20
(Shoenfield's absoluteness theorem: "every `Σ¹₂` relation is absolute for every inner model
`M` of ZF such that `ω₁ ⊆ M`"), applied to `M = L`; see also Kunen, *Set Theory*,
North-Holland 1980, Chapter VII, and Kanamori, *The Higher Infinite*, Theorem 13.15. -/
theorem lExacting_absolute (S : SilverData.{u}) (lam : Ordinal.{u}) (hlam : lam.card ≤ ℵ₀)
    (h : LExacting S lam) :
    ∃ ζ, S.Good ζ ∧ ∃ w : TWitness (S.lev ζ) lam (∅ : ZFSet.{u}),
      ∃ ξ, w.HasGraphIn (S.lev ξ) := by
  admit

end Published

end Cardinals
