/-
  REGULARITY IN THE DEFINABLE INNER MODEL
  (research note "Exacting embeddings of countable structures", Theorem 5.1(3)).

  For a witness of cofinal type, no nonempty *definable* family of cofinal subsets of `lam`
  of small order type is internally small; in particular no short cofinal subset of `lam`
  is definable.  That is the statement "`lam` is regular in `HOD_{V_lam}`".

  The note proves it by a least-counterexample device that makes the defining data fixed by
  `j`.  Here the same conclusion is obtained by the *minimal-rank-parameter* device instead
  (the mechanism of report R18 in the synthesis), which is available now that
  `fixed_below_crit` is proved: a parameter of rank below the critical point is fixed
  automatically, so a witness whose critical point is chosen *after* the parameter makes
  every parameter fixed, and `no_small_definable_family` applies.

  `HasHighWitnesses` is the hypothesis that witnesses of cofinal type exist with critical
  point above any prescribed `α < lam`.  For genuine ultraexacting cardinals it is a
  published fact ([ABL, Lemma 3.2], already admitted in `Published.lean` for
  `RelWitness`); for virtual witnesses it is part of the hypothesis, as in the note.

  Main results: `no_short_cofinal_low_rank` (`lam` is regular in the definable model),
  `no_small_family_low_rank` (Theorem 5.1(3) for parameters of rank below `lam`), and
  `least_ordinal_fixed`, the least-counterexample device, which fixes an ordinal
  parameter of any size.

  Nothing is admitted *in this file*, but the two main results inherit, through
  `fixed_below_crit`, the one admitted input of `Virtual/Restriction.lean` (definability
  of the cumulative hierarchy in a transitive model of ZF); the axiom audit shows this.
  `least_ordinal_fixed`, `leastF_spec` and `fixed_param` itself do not depend on it.
-/
import Cardinals.Virtual.Restriction

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons Free)
open SetTheory.Form

/-- `lam` has witnesses of cofinal type with critical point above any prescribed
`α < lam`. -/
def HasHighWitnesses (A : ZFSet.{u}) (lam : Ordinal.{u}) (Y : ZFSet.{u}) : Prop :=
  ∀ α < lam, ∃ w : TWitness A lam Y, w.CofinalType ∧ α < w.crit

namespace TWitness

variable {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}} (w : TWitness A lam Y)

/-- A parameter of rank below the critical point, or `lam` itself, is fixed by `j`. -/
theorem fixed_param (hZF : IsSetModelZF A) {ρ : Ordinal.{u}} (hρ : ρ < w.crit)
    {p : ZFSet.{u}} (hpA : p ∈ A) (hp : p ∈ V_ ρ ∨ p = ordZ lam) :
    ∃ hpX : p ∈ w.X, w.jv ⟨p, hpX⟩ = p := by
  rcases hp with hp | hp
  · have hplam : p ∈ V_ lam :=
      mem_vonNeumann.mpr ((mem_vonNeumann.mp hp).trans (hρ.trans w.crit_lt))
    exact ⟨w.base p hpA hplam, w.fixed_below_crit hZF ρ hρ p hp _⟩
  · subst hp
    exact ⟨w.lam_mem, w.j_lam⟩

end TWitness

/-! ### Theorem 5.1(3) by the minimal-rank-parameter device -/

/-- **No short cofinal subset of `lam` is definable from low-rank parameters**: `lam` is
regular in the inner model defined from `V_lam`.  (Note, Theorem 5.1(3), singleton case.) -/
theorem no_short_cofinal_low_rank {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}}
    (hZF : IsSetModelZF A) (hP : PairClosed A) (hhigh : HasHighWitnesses A lam Y)
    (φ : Form) (ps : ℕ → ZFSet.{u}) (ρ : Ordinal.{u}) (hρ : ρ < lam)
    (hpsA : ∀ n, ps n ∈ A) (hpsV : ∀ n, ps n ∈ V_ ρ ∨ ps n = ordZ lam)
    (a : ZFSet.{u}) (haA : a ∈ A)
    (hdef : ∀ y : Carrier A,
      Sat (memOn A) (scons y (fun n => (⟨ps n, hpsA n⟩ : Carrier A))) φ ↔ y.1 = a)
    (hcof : CofinalIn a lam)
    (hsmall : ∃ μ, μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) a) : False := by
  obtain ⟨w, hcofT, hcrit⟩ := hhigh ρ hρ
  -- every parameter is fixed, because its rank is below the critical point
  have hfix : ∀ n, ∃ h : ps n ∈ w.X, w.jv ⟨ps n, h⟩ = ps n :=
    fun n => w.fixed_param hZF hcrit (hpsA n) (hpsV n)
  choose hpsX hpsfix using hfix
  let e : ℕ → Str w.X Y := fun n => ⟨ps n, hpsX n⟩
  have hpar : ∀ k, w.j (e k) = w.up (e k) := fun k => Subtype.ext (hpsfix k)
  have henv : (fun k => w.up (e k)) = (fun n => (⟨ps n, hpsA n⟩ : Carrier A)) := by
    funext n; rfl
  -- so `a` itself is a fixed element of `X`
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed φ e hpar ⟨a, haA⟩
    (by rw [henv]; exact (hdef ⟨a, haA⟩).mpr rfl)
    (fun y hy => Subtype.ext ((hdef y).mp (by rw [← henv]; exact hy)))
  have hd1 : d.1 = a := congrArg Subtype.val hd
  have hjd1 : w.jv d = d.1 := (congrArg Subtype.val hjd).trans hd1.symm
  -- a fixed small subset of `lam` lies below the critical point, so it is not cofinal
  have hsub := w.fixed_small_subset hcofT hP d
    (by rw [hd1]; exact subOrd_iff_subset.mp hcof.1) hjd1
    (by rw [hd1]; exact hsmall)
  obtain ⟨η, hκη, -, hηa⟩ := hcof.2 w.crit w.crit_lt
  have : ordZ η ∈ ordZ w.crit := hsub (by rw [hd1]; exact hηa)
  exact absurd (Ordinal.toZFSet_mem_toZFSet_iff.mp this) (not_lt.mpr hκη)

/-- **Theorem 5.1(3).**  No nonempty family of cofinal subsets of `lam` with internally
small union is definable over `A` from parameters of rank below `lam` (and `lam`). -/
theorem no_small_family_low_rank {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}}
    (hZF : IsSetModelZF A) (hP : PairClosed A) (hhigh : HasHighWitnesses A lam Y)
    (φ : Form) (ps : ℕ → ZFSet.{u}) (ρ : Ordinal.{u}) (hρ : ρ < lam)
    (hpsA : ∀ n, ps n ∈ A) (hpsV : ∀ n, ps n ∈ V_ ρ ∨ ps n = ordZ lam)
    (F : ZFSet.{u}) (hFA : F ∈ A)
    (hdef : ∀ y : Carrier A,
      Sat (memOn A) (scons y (fun n => (⟨ps n, hpsA n⟩ : Carrier A))) φ ↔ y.1 = F)
    (hmem : ∀ b ∈ F, CofinalIn b lam) (hUA : ⋃₀ F ∈ A)
    (hsmall : ∃ μ, μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) (⋃₀ F)) : F = ∅ := by
  obtain ⟨w, hcofT, hcrit⟩ := hhigh ρ hρ
  have hfix : ∀ n, ∃ h : ps n ∈ w.X, w.jv ⟨ps n, h⟩ = ps n :=
    fun n => w.fixed_param hZF hcrit (hpsA n) (hpsV n)
  choose hpsX hpsfix using hfix
  let e : ℕ → Str w.X Y := fun n => ⟨ps n, hpsX n⟩
  have hpar : ∀ k, w.j (e k) = w.up (e k) := fun k => Subtype.ext (hpsfix k)
  have henv : (fun k => w.up (e k)) = (fun n => (⟨ps n, hpsA n⟩ : Carrier A)) := by
    funext n; rfl
  exact w.no_small_definable_family hcofT hP φ e hpar ⟨F, hFA⟩
    (by rw [henv]; exact (hdef ⟨F, hFA⟩).mpr rfl)
    (fun y hy => Subtype.ext ((hdef y).mp (by rw [← henv]; exact hy)))
    hmem hUA hsmall

/-! ### The least-counterexample device -/

/-- The renaming that shifts the parameters by one and keeps variable `0`. -/
def shiftOne : ℕ → ℕ := fun n => if n = 0 then 0 else n + 1

/-- "`v_0` satisfies `φ` and no element of `v_0` does": for ordinals, "`v_0` is the least
solution of `φ`". -/
def leastF (φ : Form) : Form :=
  fAnd φ (fAll (fImp (fMem 0 1) (fImp (SetTheory.rename shiftOne φ) fBot)))

theorem leastF_spec {A : ZFSet.{u}} (φ : Form) (e : ℕ → Carrier A) (y : Carrier A) :
    Sat (memOn A) (scons y e) (leastF φ) ↔
      (Sat (memOn A) (scons y e) φ ∧
        ∀ z : Carrier A, z.1 ∈ y.1 → ¬ Sat (memOn A) (scons z e) φ) := by
  unfold leastF
  simp only [Sat]
  refine and_congr Iff.rfl ⟨fun h z hz hsat => ?_, fun h z hz hsat => ?_⟩
  · refine h z hz ?_
    rw [SetTheory.Sat_rename]
    refine (SetTheory.Sat_ext φ _ _ (fun n => ?_)).mpr hsat
    cases n with
    | zero => rfl
    | succ m => rfl
  · rw [SetTheory.Sat_rename] at hsat
    refine h z hz ((SetTheory.Sat_ext φ _ _ (fun n => ?_)).mp hsat)
    cases n with
    | zero => rfl
    | succ m => rfl

namespace TWitness

variable {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}} (w : TWitness A lam Y)

/-- **The least-counterexample device.**  If `φ`, with parameters fixed by `j`, is
satisfied in `A` only by ordinals, then the *least* ordinal satisfying it is fixed by `j`
-- however large it is, and although `j` moves cofinally many ordinals.  This is what makes
the minimization of the note's Theorem 5.1(3) work, and it needs no satisfaction predicate
inside `A`, because `leastF` is built from `φ` at the meta-level. -/
theorem least_ordinal_fixed (e : ℕ → Str w.X Y) (hpar : ∀ k, w.j (e k) = w.up (e k))
    (φ : Form) (γ : Ordinal.{u}) (hγ : γ < lam)
    (hord : ∀ y : Carrier A, Sat (memOn A) (scons y (fun k => w.up (e k))) φ →
      ∃ δ, δ < lam ∧ y.1 = ordZ δ)
    (hsat : Sat (memOn A) (scons (w.up (w.ordX γ hγ)) (fun k => w.up (e k))) φ)
    (hmin : ∀ δ : Ordinal.{u}, ∀ hδ : δ < γ,
      ¬ Sat (memOn A) (scons (w.up (w.ordX δ (hδ.trans hγ))) (fun k => w.up (e k))) φ) :
    w.jOrd γ = γ := by
  have hγA : ordZ γ ∈ A := w.ord_mem_A hγ
  have hup : ∀ (δ : Ordinal.{u}) (hδ : δ < lam) (hA : ordZ δ ∈ A),
      (⟨ordZ δ, hA⟩ : Carrier A) = w.up (w.ordX δ hδ) := fun _ _ _ => rfl
  -- `ordZ γ` is the unique solution of `leastF φ`
  have hsol : Sat (memOn A) (scons (⟨ordZ γ, hγA⟩ : Carrier A) (fun k => w.up (e k)))
      (leastF φ) := by
    refine (leastF_spec φ _ _).mpr ⟨?_, fun z hz hzsat => ?_⟩
    · rw [hup γ hγ hγA]; exact hsat
    · have hz' : z.1 ∈ ordZ γ := hz
      obtain ⟨δ, hδ, hzeq⟩ := Ordinal.mem_toZFSet_iff.mp hz'
      have hzc : z = w.up (w.ordX δ (hδ.trans hγ)) := Subtype.ext hzeq.symm
      rw [hzc] at hzsat
      exact hmin δ hδ hzsat
  have huniq : ∀ y : Carrier A,
      Sat (memOn A) (scons y (fun k => w.up (e k))) (leastF φ) → y = ⟨ordZ γ, hγA⟩ := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := (leastF_spec φ _ _).mp hy
    obtain ⟨δ, hδlam, hyδ⟩ := hord y hy1
    have hyc : y = w.up (w.ordX δ hδlam) := Subtype.ext hyδ
    apply Subtype.ext
    show y.1 = ordZ γ
    rw [hyδ]
    rcases lt_trichotomy δ γ with h | h | h
    · rw [hyc] at hy1
      exact absurd hy1 (hmin δ h)
    · rw [h]
    · refine absurd hsat (?_ : ¬ _)
      have hmemγ : (⟨ordZ γ, hγA⟩ : Carrier A).1 ∈ y.1 := by
        rw [hyδ]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr h
      have := hy2 ⟨ordZ γ, hγA⟩ hmemγ
      rwa [hup γ hγ hγA] at this
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed (leastF φ) e hpar ⟨ordZ γ, hγA⟩ hsol huniq
  have hd0 : d.1 = ordZ γ := congrArg Subtype.val hd
  have hd1 : d = w.ordX γ hγ := Subtype.ext hd0
  have hjd1 : w.jv d = ordZ γ := congrArg Subtype.val hjd
  rw [hd1, jv_ordX] at hjd1
  exact ordZ_inj hjd1

end TWitness

end Cardinals
