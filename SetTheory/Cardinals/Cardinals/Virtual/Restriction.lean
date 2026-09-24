/-
  THE RESTRICTION TO THE RANK SEGMENT IS ELEMENTARY
  (research note "Exacting embeddings of countable structures", Theorem 3.1(4)).

  For `w : TWitness A lam Y` over a transitive model `A` of ZF, the restriction of `j` to
  `V_lam^A` is an elementary embedding of `(V_lam^A, ∈)` into itself with critical point
  `crit(j)`.  In the note this is what makes `crit(j)` *virtually rank-into-rank*.

  Two ingredients are new here.

  * `relTo k φ` relativizes every quantifier of a ProveIt formula to the variable `v_k`,
    and `relTo_spec` proves that `A ⊨ (relTo k φ)[e]` iff `(e k, ∈) ⊨ φ[e]`.  This is what
    replaces a satisfaction predicate *inside* `A`: elementarity is a statement about each
    formula separately, so a formula-by-formula translation suffices.
  * `fixed_below_crit`: `j` fixes every element of `V_ρ^A` for `ρ < crit(j)`, by induction
    on `ρ`.  (For `ρ = crit` this fails: `crit` is moved.)

  One published input is admitted: `Published.exists_vonNeumann_formula`, the definability
  of the cumulative hierarchy in a transitive model of ZF.

  Main results: `vA_fixed`, `fixed_below_crit`, `restriction_elementary`,
  `restriction_moves_crit`, `restriction_elementary_of_relWitness`.
-/
import Cardinals.Virtual.Extras

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons Free)
open SetTheory.Form

/-! ### Relativization of formulas -/

/-- `relTo k φ` is `φ` with every quantifier restricted to the members of `v_k`. -/
def relTo : ℕ → Form → Form
  | _, fMem i j => fMem i j
  | _, fEq i j => fEq i j
  | _, fBot => fBot
  | k, fImp a b => fImp (relTo k a) (relTo k b)
  | k, fAnd a b => fAnd (relTo k a) (relTo k b)
  | k, fOr a b => fOr (relTo k a) (relTo k b)
  | k, fAll a => fAll (fImp (fMem 0 (k + 1)) (relTo (k + 1) a))
  | k, fEx a => fEx (fAnd (fMem 0 (k + 1)) (relTo (k + 1) a))

/-- **The relativization theorem.**  Satisfaction of `relTo k φ` in `A`, with the value of
`v_k` equal to `u ⊆ A`, is satisfaction of `φ` in the structure `(u, ∈)`. -/
theorem relTo_spec {A u : ZFSet.{u}} (hu : u ⊆ A) :
    ∀ (φ : Form) (k : ℕ) (e : ℕ → Carrier A) (e' : ℕ → Carrier u),
      ¬ Free k φ → (e k).1 = u → (∀ n, n ≠ k → (e' n).1 = (e n).1) →
      (Sat (memOn A) e (relTo k φ) ↔ Sat (memOn u) e' φ) := by
  intro φ
  induction φ with
  | fMem i j =>
    intro k e e' hk hek hag
    have hi : i ≠ k := fun h => hk (Or.inl h.symm)
    have hj : j ≠ k := fun h => hk (Or.inr h.symm)
    show (e i).1 ∈ (e j).1 ↔ (e' i).1 ∈ (e' j).1
    rw [hag i hi, hag j hj]
  | fEq i j =>
    intro k e e' hk hek hag
    have hi : i ≠ k := fun h => hk (Or.inl h.symm)
    have hj : j ≠ k := fun h => hk (Or.inr h.symm)
    show e i = e j ↔ e' i = e' j
    constructor
    · intro h
      exact Subtype.ext ((hag i hi).trans (congrArg Subtype.val h) |>.trans (hag j hj).symm)
    · intro h
      exact Subtype.ext ((hag i hi).symm.trans (congrArg Subtype.val h) |>.trans (hag j hj))
  | fBot => intro k e e' _ _ _; exact Iff.rfl
  | fImp a b iha ihb =>
    intro k e e' hk hek hag
    exact imp_congr (iha k e e' (fun h => hk (Or.inl h)) hek hag)
      (ihb k e e' (fun h => hk (Or.inr h)) hek hag)
  | fAnd a b iha ihb =>
    intro k e e' hk hek hag
    exact and_congr (iha k e e' (fun h => hk (Or.inl h)) hek hag)
      (ihb k e e' (fun h => hk (Or.inr h)) hek hag)
  | fOr a b iha ihb =>
    intro k e e' hk hek hag
    exact or_congr (iha k e e' (fun h => hk (Or.inl h)) hek hag)
      (ihb k e e' (fun h => hk (Or.inr h)) hek hag)
  | fAll a iha =>
    intro k e e' hk hek hag
    show (∀ d : Carrier A, Sat (memOn A) (scons d e) (fImp (fMem 0 (k + 1)) (relTo (k + 1) a)))
      ↔ ∀ d' : Carrier u, Sat (memOn u) (scons d' e') a
    constructor
    · intro h d'
      have hd : d'.1 ∈ A := hu d'.2
      have hmem : (scons (⟨d'.1, hd⟩ : Carrier A) e 0).1 ∈ (scons (⟨d'.1, hd⟩ : Carrier A) e (k + 1)).1 := by
        show d'.1 ∈ (e k).1
        rw [hek]; exact d'.2
      refine (iha (k + 1) (scons ⟨d'.1, hd⟩ e) (scons d' e') hk hek
        (fun n hn => ?_)).mp (h ⟨d'.1, hd⟩ hmem)
      cases n with
      | zero => rfl
      | succ m => exact hag m (fun h' => hn (by rw [h']))
    · intro h d hd
      have hdu : d.1 ∈ u := by
        have : d.1 ∈ (e k).1 := hd
        rwa [hek] at this
      refine (iha (k + 1) (scons d e) (scons ⟨d.1, hdu⟩ e') hk hek
        (fun n hn => ?_)).mpr (h ⟨d.1, hdu⟩)
      cases n with
      | zero => rfl
      | succ m => exact hag m (fun h' => hn (by rw [h']))
  | fEx a iha =>
    intro k e e' hk hek hag
    show (∃ d : Carrier A, Sat (memOn A) (scons d e) (fAnd (fMem 0 (k + 1)) (relTo (k + 1) a)))
      ↔ ∃ d' : Carrier u, Sat (memOn u) (scons d' e') a
    constructor
    · rintro ⟨d, hd, hsat⟩
      have hdu : d.1 ∈ u := by
        have : d.1 ∈ (e k).1 := hd
        rwa [hek] at this
      refine ⟨⟨d.1, hdu⟩, (iha (k + 1) (scons d e) (scons ⟨d.1, hdu⟩ e') hk hek
        (fun n hn => ?_)).mp hsat⟩
      cases n with
      | zero => rfl
      | succ m => exact hag m (fun h' => hn (by rw [h']))
    · rintro ⟨d', hsat⟩
      have hd : d'.1 ∈ A := hu d'.2
      refine ⟨⟨d'.1, hd⟩, ?_, (iha (k + 1) (scons ⟨d'.1, hd⟩ e) (scons d' e') hk
        hek (fun n hn => ?_)).mpr hsat⟩
      · show d'.1 ∈ (e k).1
        rw [hek]; exact d'.2
      · cases n with
        | zero => rfl
        | succ m => exact hag m (fun h' => hn (by rw [h']))

/-! ### The rank segments of a model -/

/-- The `ρ`-th stage of the cumulative hierarchy as computed in `A`. -/
noncomputable def vA (A : ZFSet.{u}) (ρ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun t => t ∈ V_ ρ) A

theorem mem_vA {A : ZFSet.{u}} {ρ : Ordinal.{u}} {t : ZFSet.{u}} :
    t ∈ vA A ρ ↔ t ∈ A ∧ t ∈ V_ ρ := mem_sep

theorem vA_subset {A : ZFSet.{u}} {ρ : Ordinal.{u}} : vA A ρ ⊆ A :=
  fun _ ht => (mem_vA.mp ht).1

theorem vA_mono {A : ZFSet.{u}} {ρ σ : Ordinal.{u}} (h : ρ ≤ σ) : vA A ρ ⊆ vA A σ := by
  intro t ht
  obtain ⟨h1, h2⟩ := mem_vA.mp ht
  rw [mem_vonNeumann] at h2
  exact mem_vA.mpr ⟨h1, mem_vonNeumann.mpr (h2.trans_le h)⟩

/-- `A` satisfies the axioms of ZF. -/
def IsSetModelZF (A : ZFSet.{u}) : Prop :=
  ∀ φ, SetTheory.ZFax φ → ∀ e : ℕ → Carrier A, Sat (memOn A) e φ

theorem IsSetModelZFC.toZF {A : ZFSet.{u}} (h : IsSetModelZFC A) : IsSetModelZF A := h.1

namespace Published

/-- **The cumulative hierarchy is definable in a transitive model of ZF.**  There is a
single formula `vF` such that, for every ordinal `ρ` of `A`, the stage `V_ρ ∩ A` is an
element of `A` and is the unique `y ∈ A` with `A ⊨ vF[y, ρ]`.

Reference: T. Jech, "Set Theory", 3rd millennium ed., Springer 2003, Chapter 6 (the
cumulative hierarchy `V_α`, defined by transfinite recursion, with `V_α ∈ M` for every
ordinal `α` of a transitive model `M` of ZF) together with Chapter 12, in particular the
absoluteness of the rank function and of `V_α` for transitive models of ZF (the defining
recursion is `Δ₁` and therefore absolute).  See also K. Kunen, "Set Theory: An
Introduction to Independence Proofs", North-Holland 1980, Chapter IV §3 (absoluteness of
`R(α)` for transitive models of ZF minus power set plus the relevant instances). -/
theorem exists_vonNeumann_formula {A : ZFSet.{u}} (hZF : IsSetModelZF A) :
    ∃ vF : Form, ∀ (ρ : Ordinal.{u}) (hρ : ordZ ρ ∈ A),
      vA A ρ ∈ A ∧
      ∀ y : Carrier A,
        (Sat (memOn A) (scons y (fun _ => (⟨ordZ ρ, hρ⟩ : Carrier A))) vF ↔ y.1 = vA A ρ) := by
  admit

end Published

namespace TWitness

variable {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}} (w : TWitness A lam Y)

theorem subset_iff (x y : Str w.X Y) : x.1 ⊆ y.1 ↔ w.jv x ⊆ w.jv y := by
  have h := w.elem (subsetF 0 1) (scons x (fun _ => y))
  rw [subsetF_spec w.trans, subsetF_spec w.trans] at h
  exact h

/-- Each stage `V_ρ^A` with `ρ` fixed by `j` is an element of `X` fixed by `j`. -/
theorem vA_fixed (hZF : IsSetModelZF A) {ρ : Ordinal.{u}} (hρ : ρ < lam)
    (hfix : w.jOrd ρ = ρ) : ∃ v : Str w.X Y, v.1 = vA A ρ ∧ w.jv v = vA A ρ := by
  obtain ⟨vF, hvF⟩ := Published.exists_vonNeumann_formula hZF
  obtain ⟨hmem, huniq⟩ := hvF ρ (w.ord_mem_A hρ)
  have hpar : ∀ k : ℕ, w.j ((fun _ => w.ordX ρ hρ) k) = w.up ((fun _ => w.ordX ρ hρ) k) := by
    intro _
    apply Subtype.ext
    show w.jv (w.ordX ρ hρ) = ordZ ρ
    rw [jv_ordX, hfix]
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed vF (fun _ => w.ordX ρ hρ) hpar ⟨vA A ρ, hmem⟩
    ((huniq ⟨vA A ρ, hmem⟩).mpr rfl) (fun y hy => Subtype.ext ((huniq y).mp hy))
  exact ⟨d, congrArg Subtype.val hd, congrArg Subtype.val hjd⟩

/-- The top stage `V_lam^A` is an element of `X` fixed by `j`. -/
theorem vA_lam_fixed (hZF : IsSetModelZF A) :
    ∃ v : Str w.X Y, v.1 = vA A lam ∧ w.jv v = vA A lam := by
  obtain ⟨vF, hvF⟩ := Published.exists_vonNeumann_formula hZF
  obtain ⟨hmem, huniq⟩ := hvF lam w.lam_mem_A
  have hpar : ∀ k : ℕ, w.j ((fun _ => w.lamX) k) = w.up ((fun _ => w.lamX) k) := by
    intro _
    exact Subtype.ext w.j_lam
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed vF (fun _ => w.lamX) hpar ⟨vA A lam, hmem⟩
    ((huniq ⟨vA A lam, hmem⟩).mpr rfl) (fun y hy => Subtype.ext ((huniq y).mp hy))
  exact ⟨d, congrArg Subtype.val hd, congrArg Subtype.val hjd⟩

/-- **`j` fixes every set of rank below the critical point.**  (For `ρ = crit` this fails:
the critical point is moved.) -/
theorem fixed_below_crit (hZF : IsSetModelZF A) :
    ∀ ρ : Ordinal.{u}, ρ < w.crit → ∀ z : ZFSet.{u}, z ∈ V_ ρ → ∀ hzX : z ∈ w.X,
      w.jv ⟨z, hzX⟩ = z := by
  intro ρ
  induction ρ using WellFoundedLT.induction with
  | _ ρ ih =>
    intro hρ z hz hzX
    have hρlam : ρ < lam := hρ.trans w.crit_lt
    set σ : Ordinal.{u} := ZFSet.rank z with hσdef
    have hσρ : σ < ρ := by rw [hσdef]; exact mem_vonNeumann.mp hz
    have hσcrit : σ < w.crit := hσρ.trans hρ
    have hσlam : σ < lam := hσcrit.trans w.crit_lt
    -- `z ⊆ V_σ^A`
    have hzsub : z ⊆ vA A σ := by
      intro t ht
      refine mem_vA.mpr ⟨w.trans.subset_of_mem (w.X_sub hzX) ht, ?_⟩
      rw [mem_vonNeumann, hσdef]
      exact rank_lt_of_mem ht
    obtain ⟨v, hv, hvfix⟩ := w.vA_fixed hZF hσlam (w.jOrd_of_lt_crit hσcrit)
    -- elements of `z` are fixed, so `z ⊆ j z`
    have hmemX : ∀ t ∈ z, t ∈ w.X := fun t ht =>
      w.base t (w.trans.subset_of_mem (w.X_sub hzX) ht)
        (mem_vonNeumann.mpr ((mem_vonNeumann.mp (mem_vA.mp (hzsub ht)).2).trans hσlam))
    have hfixmem : ∀ t, ∀ ht : t ∈ z, w.jv ⟨t, hmemX t ht⟩ = t := fun t ht =>
      ih σ hσρ hσcrit t (mem_vA.mp (hzsub ht)).2 (hmemX t ht)
    -- `j z ⊆ V_σ^A`
    have hjsub : w.jv ⟨z, hzX⟩ ⊆ vA A σ := by
      have h1 : (⟨z, hzX⟩ : Str w.X Y).1 ⊆ v.1 := by rw [hv]; exact hzsub
      have h2 := (w.subset_iff ⟨z, hzX⟩ v).mp h1
      rwa [hvfix] at h2
    ext t
    constructor
    · intro ht
      have htA : t ∈ A := (mem_vA.mp (hjsub ht)).1
      have htV : t ∈ V_ σ := (mem_vA.mp (hjsub ht)).2
      have htX : t ∈ w.X :=
        w.base t htA (mem_vonNeumann.mpr ((mem_vonNeumann.mp htV).trans hσlam))
      have htfix : w.jv ⟨t, htX⟩ = t := ih σ hσρ hσcrit t htV htX
      have := (w.mem_iff ⟨t, htX⟩ ⟨z, hzX⟩).mpr (by rw [htfix]; exact ht)
      exact this
    · intro ht
      have := (w.mem_iff ⟨t, hmemX t ht⟩ ⟨z, hzX⟩).mp ht
      rwa [hfixmem t ht] at this

/-! ### Theorem 3.1(4): the restriction is elementary -/

theorem jv_mem_vA_lam (hZF : IsSetModelZF A) {v : Str w.X Y} (hv : v.1 = vA A lam)
    (hvfix : w.jv v = vA A lam) (x : Str w.X Y) (hx : x.1 ∈ vA A lam) :
    w.jv x ∈ vA A lam := by
  have h1 : x.1 ∈ v.1 := by rw [hv]; exact hx
  have h2 := (w.mem_iff x v).mp h1
  rwa [hvfix] at h2

/-- **The restriction of `j` to the rank segment `V_lam^A` is elementary**
(note, Theorem 3.1(4)).  Stated formula by formula, which is what elementarity means; no
satisfaction predicate inside `A` is needed, because `relTo` translates each formula. -/
theorem restriction_elementary (hZF : IsSetModelZF A) {v : Str w.X Y} (hv : v.1 = vA A lam)
    (hvfix : w.jv v = vA A lam) (φ : Form) (m : ℕ) (hm : ∀ n, Free n φ → n < m)
    (x : ℕ → Str w.X Y) (hx : ∀ n, (x n).1 ∈ vA A lam) :
    Sat (memOn (vA A lam)) (fun n => (⟨(x n).1, hx n⟩ : Carrier (vA A lam))) φ ↔
      Sat (memOn (vA A lam))
        (fun n => (⟨w.jv (x n), w.jv_mem_vA_lam hZF hv hvfix (x n) (hx n)⟩ :
          Carrier (vA A lam))) φ := by
  have hsub : vA A lam ⊆ A := vA_subset
  have hmfree : ¬ Free m φ := fun h => lt_irrefl m (hm m h)
  -- the environment in `X` that carries the parameters and, at index `m`, the segment
  let p : ℕ → Str w.X Y := fun n => if n = m then v else x n
  have hel := w.elem (relTo m φ) p
  -- left-hand side
  have hL : Sat (memOn A) (fun k => w.up (p k)) (relTo m φ) ↔
      Sat (memOn (vA A lam)) (fun n => (⟨(x n).1, hx n⟩ : Carrier (vA A lam))) φ := by
    refine relTo_spec hsub φ m (fun k => w.up (p k))
      (fun n => (⟨(x n).1, hx n⟩ : Carrier (vA A lam))) hmfree ?_ ?_
    · show (p m).1 = vA A lam
      simp only [p, if_pos rfl, hv]
    · intro n hn
      show (x n).1 = (p n).1
      simp only [p, if_neg hn]
  -- right-hand side
  have hR : Sat (memOn A) (fun k => w.j (p k)) (relTo m φ) ↔
      Sat (memOn (vA A lam))
        (fun n => (⟨w.jv (x n), w.jv_mem_vA_lam hZF hv hvfix (x n) (hx n)⟩ :
          Carrier (vA A lam))) φ := by
    refine relTo_spec hsub φ m (fun k => w.j (p k)) _ hmfree ?_ ?_
    · show w.jv (p m) = vA A lam
      simp only [p, if_pos rfl]
      exact hvfix
    · intro n hn
      show w.jv (x n) = w.jv (p n)
      simp only [p, if_neg hn]
  rw [← hL, ← hR]
  exact hel

/-- The restriction is nontrivial, with critical point `crit(j)`. -/
theorem restriction_moves_crit (hZF : IsSetModelZF A) :
    ordZ w.crit ∈ vA A lam ∧ w.jv (w.ordX w.crit w.crit_lt) ≠ ordZ w.crit ∧
      ∀ (ξ : Ordinal.{u}) (hξ : ξ < w.crit),
        w.jv (w.ordX ξ (hξ.trans w.crit_lt)) = ordZ ξ := by
  refine ⟨mem_vA.mpr ⟨w.ord_mem_A w.crit_lt, ordZ_mem_V w.crit_lt⟩, ?_, ?_⟩
  · rw [jv_ordX]
    exact fun h => w.jOrd_crit_ne (ordZ_inj h)
  · intro ξ hξ
    rw [jv_ordX, w.jOrd_of_lt_crit hξ]

end TWitness

/-- For a genuine witness of limit height, the restriction of `j` to `V_lam` is an
elementary embedding of `V_lam` into itself. -/
theorem RelWitness.restriction_elementary {lam α : Ordinal.{u}} {Y : ZFSet.{u}}
    (w : RelWitness lam α Y) (hZF : IsSetModelZF (V_ α)) :
    ∃ v : Str w.toTWitness.X Y, v.1 = vA (V_ α) lam ∧ w.toTWitness.jv v = vA (V_ α) lam :=
  w.toTWitness.vA_lam_fixed hZF

end Cardinals
