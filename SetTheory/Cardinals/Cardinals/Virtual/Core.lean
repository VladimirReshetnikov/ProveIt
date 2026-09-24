/-
  THE KUNEN-FREE CORE AND THE COFINAL-TYPE THEOREMS FOR WITNESSES OVER A TRANSITIVE MODEL
  (research note "Exacting embeddings of countable structures", Theorems 3.1 and 5.1).

  `w : TWitness A lam Y`, with `A` a transitive, pair-closed set in which `lam` is a limit
  ordinal.  All notions of size are *internal to `A`*: "small" means "the image of an
  ordinal below `lam` under a function that belongs to `A`", and the power set is
  `powA A y = 𝒫(y) ∩ A`.  So the theorems apply to countable `A` (where true cardinalities
  are meaningless) and to `A = V_ζ` of a ground model, with an embedding `j ∉ A`.

  Theorem 3.1 (no assumption on the critical sequence):
  * `jOrd_nat`, `jOrd_omega`, `omega_le_crit`;
  * `jv_subset_fixed`: `j` fixes every subset (in `A`) of an ordinal below `crit`;
  * `no_surj_pow_crit`, `slSem_critSeq`: no function in `A` maps `𝒫^A(μ)` onto `κ_n`, `μ < κ_n`;
  * `crit_regular`: no function in `A` maps `μ < κ` onto a cofinal subset of `κ`.
  Theorem 5.1 (for witnesses of cofinal type, `w.CofinalType`):
  * `fixed_small_subset`: a fixed internally small `S ⊆ lam` in `X` lies below `crit`;
  * `no_small_fixed_family`, `no_small_definable_family`: there is no nonempty fixed --
    in particular no nonempty definable-from-fixed-parameters -- family of cofinal subsets
    of `lam` whose union is internally small.

  Nothing is admitted in this file, and nothing in it depends on an admitted statement.
-/
import Cardinals.Virtual.TWitness
import Cardinals.CoverBound

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

/-! ### Internal power sets -/

/-- The power set of `y` in the sense of `A`. -/
noncomputable def powA (A y : ZFSet.{u}) : ZFSet.{u} := ZFSet.sep (fun t => t ∈ A) (powerset y)

theorem mem_powA {A y t : ZFSet.{u}} : t ∈ powA A y ↔ t ∈ A ∧ t ⊆ y := by
  unfold powA
  rw [mem_sep, mem_powerset]
  exact and_comm

theorem powF_specA {A : ZFSet.{u}} (hA : IsTransitive A) (e : ℕ → Carrier A) (i j : ℕ) :
    Sat (memOn A) e (powF i j) ↔ (e i).1 = powA A (e j).1 := by
  unfold powF
  simp only [Sat, SetTheory.Sat_fIff]
  constructor
  · intro h
    ext t
    rw [mem_powA]
    constructor
    · intro ht
      have htA : t ∈ A := hA.subset_of_mem (e i).2 ht
      exact ⟨htA, (subsetF_spec hA _ 0 (j + 1)).mp ((h ⟨t, htA⟩).mp ht)⟩
    · rintro ⟨htA, ht⟩
      exact (h ⟨t, htA⟩).mpr ((subsetF_spec hA _ 0 (j + 1)).mpr ht)
  · intro h d
    rw [subsetF_spec hA]
    show d.1 ∈ (e i).1 ↔ d.1 ⊆ (e j).1
    rw [h, mem_powA]
    exact ⟨fun x => x.2, fun x => ⟨d.2, x⟩⟩

/-- No element `μ` of `k` has its internal power set mapped onto `k` by a function in `A`. -/
def SLSemA (A k : ZFSet.{u}) : Prop := ∀ μ ∈ k, ¬ ∃ f ∈ A, SurjSem A f (powA A μ) k

theorem slF_specA {A : ZFSet.{u}} (hA : IsTransitive A) (hP : PairClosed A)
    (hpow : ∀ y ∈ A, powA A y ∈ A) (e : ℕ → Carrier A) (k : ℕ) :
    Sat (memOn A) e (slF k) ↔ SLSemA A (e k).1 := by
  unfold slF SLSemA
  simp only [Sat]
  constructor
  · rintro h μ hμ ⟨f, hf, hs⟩
    have hμA : μ ∈ A := hA.subset_of_mem (e k).2 hμ
    exact h ⟨μ, hμA⟩ hμ ⟨powA A μ, hpow μ hμA⟩ ((powF_specA hA _ 0 1).mpr rfl)
      ⟨⟨f, hf⟩, (surjF_spec hA hP _ 0 1 (k + 3)).mpr hs⟩
  · rintro h d hd p hp ⟨f, hf⟩
    have hp' : p.1 = powA A d.1 := (powF_specA hA _ 0 1).mp hp
    have hf' : SurjSem A f.1 p.1 (e k).1 := (surjF_spec hA hP _ 0 1 (k + 3)).mp hf
    rw [hp'] at hf'
    exact h d.1 hd ⟨f.1, f.2, hf'⟩

namespace TWitness

variable {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}} (w : TWitness A lam Y)

/-! ### Transfer lemmas -/

theorem nonempty_iff (b : Str w.X Y) : (∃ t, t ∈ b.1) ↔ ∃ t, t ∈ w.jv b := by
  have h := w.elem (nonemptyF 0) (fun _ => b)
  rw [nonemptyF_spec w.trans, nonemptyF_spec w.trans] at h
  exact h

theorem insert_iff (b x b' : Str w.X Y) :
    b.1 = insert x.1 b'.1 ↔ w.jv b = insert (w.jv x) (w.jv b') := by
  have h := w.elem (insertF 0 1 2) (scons b (scons x (fun _ => b')))
  rw [insertF_spec w.trans, insertF_spec w.trans] at h
  exact h

theorem inter_iff (b x y : Str w.X Y) :
    b.1 = x.1 ∩ y.1 ↔ w.jv b = w.jv x ∩ w.jv y := by
  have h := w.elem (interF 0 1 2) (scons b (scons x (fun _ => y)))
  rw [interF_spec w.trans, interF_spec w.trans] at h
  exact h

theorem sUnion_iff (u F : Str w.X Y) : u.1 = ⋃₀ F.1 ↔ w.jv u = ⋃₀ (w.jv F) := by
  have h := w.elem (sUnionF 0 1) (scons u (fun _ => F))
  rw [sUnionF_spec w.trans, sUnionF_spec w.trans] at h
  exact h

theorem pair_mem_iff (hP : PairClosed A) (x y f : Str w.X Y) :
    pair x.1 y.1 ∈ f.1 ↔ pair (w.jv x) (w.jv y) ∈ w.jv f := by
  have h := w.elem (pairMemF 0 1 2) (scons x (scons y (fun _ => f)))
  rw [pairMemF_spec w.trans hP, pairMemF_spec w.trans hP] at h
  exact h

theorem surj_iff (hP : PairClosed A) (f m S : Str w.X Y) :
    SurjSem A f.1 m.1 S.1 ↔ SurjSem A (w.jv f) (w.jv m) (w.jv S) := by
  have h := w.elem (surjF 0 1 2) (scons f (scons m (fun _ => S)))
  rw [surjF_spec w.trans hP, surjF_spec w.trans hP] at h
  exact h

theorem surj_in_X (hP : PairClosed A) (m S : Str w.X Y)
    (h : ∃ f ∈ A, SurjSem A f m.1 S.1) : ∃ f : Str w.X Y, SurjSem A f.1 m.1 S.1 := by
  obtain ⟨f, hfA, hfs⟩ := h
  obtain ⟨d, hd⟩ := w.tarski_vaught (surjF 0 1 2) (scons m (fun _ => S))
    ⟨⟨f, hfA⟩, (surjF_spec w.trans hP _ 0 1 2).mpr hfs⟩
  exact ⟨d, (surjF_spec w.trans hP _ 0 1 2).mp hd⟩

theorem pow_iff (p m : Str w.X Y) : p.1 = powA A m.1 ↔ w.jv p = powA A (w.jv m) := by
  have h := w.elem (powF 0 1) (scons p (fun _ => m))
  rw [powF_specA w.trans, powF_specA w.trans] at h
  exact h

theorem sl_iff (hP : PairClosed A) (hpow : ∀ y ∈ A, powA A y ∈ A) (k : Str w.X Y) :
    SLSemA A k.1 ↔ SLSemA A (w.jv k) := by
  have h := w.elem (slF 0) (fun _ => k)
  rw [slF_specA w.trans hP hpow, slF_specA w.trans hP hpow] at h
  exact h

theorem cof_iff (S k : Str w.X Y) : CofSem S.1 k.1 ↔ CofSem (w.jv S) (w.jv k) := by
  have h := w.elem (cofF 0 1) (scons S (fun _ => k))
  rw [cofF_spec w.trans, cofF_spec w.trans] at h
  exact h

theorem noLimit_iff (x : Str w.X Y) : NoLimitSem x.1 ↔ NoLimitSem (w.jv x) := by
  have h := w.elem (noLimitF 0) (fun _ => x)
  rw [noLimitF_spec w.trans, noLimitF_spec w.trans] at h
  exact h

theorem ord_mem_iff {ξ : Ordinal.{u}} (hξ : ξ < lam) (S : Str w.X Y) :
    ordZ ξ ∈ S.1 ↔ ordZ (w.jOrd ξ) ∈ w.jv S := by
  have := w.mem_iff (w.ordX ξ hξ) S
  rwa [jv_ordX] at this

/-- Every member of `A` that is a subset of an ordinal below `lam` belongs to `X`. -/
theorem mem_X_of_subset_ord {x : ZFSet.{u}} (hxA : x ∈ A) {μ : Ordinal.{u}} (hμ : μ < lam)
    (hx : x ⊆ ordZ μ) : x ∈ w.X :=
  w.base x hxA (mem_V_of_subset (β := μ) (fun t ht => ordZ_subset_V _ (hx ht)) hμ)

/-! ### Theorem 3.1(1): finite ordinals and `ω` -/

theorem jOrd_zero : w.jOrd 0 = 0 := by
  have h0 : (0 : Ordinal.{u}) < lam := lt_of_le_of_lt zero_le w.crit_lt
  by_contra hne
  have hpos : 0 < w.jOrd 0 := pos_iff_ne_zero.mpr hne
  have hex : ∃ t, t ∈ w.jv (w.ordX 0 h0) :=
    ⟨ordZ 0, by rw [jv_ordX]; exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hpos⟩
  obtain ⟨t, ht⟩ := (w.nonempty_iff _).mpr hex
  have ht' : t ∈ (∅ : ZFSet.{u}) := by
    rw [← Ordinal.toZFSet_zero]
    exact ht
  exact ZFSet.notMem_empty t ht'

theorem jOrd_add_one {ξ : Ordinal.{u}} (h : ξ + 1 < lam) : w.jOrd (ξ + 1) = w.jOrd ξ + 1 := by
  have hξ : ξ < lam := lt_trans (Order.lt_add_one_iff.mpr le_rfl) h
  have h1 : (w.ordX (ξ + 1) h).1 = insert (w.ordX ξ hξ).1 (w.ordX ξ hξ).1 :=
    Ordinal.toZFSet_add_one ξ
  have h2 := (w.insert_iff _ _ _).mp h1
  rw [jv_ordX, jv_ordX, ← Ordinal.toZFSet_add_one] at h2
  exact ordZ_inj h2

theorem jOrd_nat (hω : ω ≤ lam) (n : ℕ) : w.jOrd (n : Ordinal.{u}) = n := by
  induction n with
  | zero => simpa using w.jOrd_zero
  | succ n ih =>
    have hlt : ((n : Ordinal.{u}) + 1) < lam := by
      have := Ordinal.natCast_lt_omega0 (n + 1)
      rw [Nat.cast_succ] at this
      exact this.trans_le hω
    rw [Nat.cast_succ, w.jOrd_add_one hlt, ih]

/-- The critical point is infinite. -/
theorem omega_le_crit (hω : ω ≤ lam) : ω ≤ w.crit := by
  by_contra h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (not_le.mp h)
  exact w.jOrd_crit_ne (by rw [hn, w.jOrd_nat hω])

theorem jOrd_omega (hω : ω ≤ lam) : w.jOrd ω = ω := by
  have hωlam : ω < lam := (w.omega_le_crit hω).trans_lt w.crit_lt
  by_contra hne
  have hlt : ω < w.jOrd ω := lt_of_le_of_ne (w.le_jOrd hωlam) (Ne.symm hne)
  have h1 := (w.noLimit_iff (w.ordX ω hωlam)).mp RelWitness.noLimitSem_omega
  rw [jv_ordX] at h1
  rcases h1 (ordZ ω) (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt) with h0 | ⟨z, hz, hins⟩
  · have : ordZ (0 : Ordinal.{u}) ∈ ordZ (ω : Ordinal.{u}) :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr Ordinal.omega0_pos
    rw [h0] at this
    exact ZFSet.notMem_empty _ this
  · obtain ⟨ζ, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    rw [← Ordinal.toZFSet_add_one] at hins
    have hζ : ω = ζ + 1 := ordZ_inj hins
    have hζlt : ζ < ω := by rw [hζ]; exact Order.lt_add_one_iff.mpr le_rfl
    have := Ordinal.isSuccLimit_omega0.succ_lt hζlt
    rw [Order.succ_eq_add_one, ← hζ] at this
    exact lt_irrefl _ this

/-! ### Theorem 3.1(2): small sets of ordinals are fixed -/

theorem jv_subset_fixed (x : Str w.X Y) {μ : Ordinal.{u}} (hμ : μ < w.crit)
    (hx : x.1 ⊆ ordZ μ) : w.jv x = x.1 := by
  have hμlam : μ < lam := hμ.trans w.crit_lt
  have h1 : x.1 = x.1 ∩ (w.ordX μ hμlam).1 := by
    ext t
    rw [mem_inter]
    exact ⟨fun ht => ⟨ht, hx ht⟩, fun ht => ht.1⟩
  have h2 := (w.inter_iff x x (w.ordX μ hμlam)).mp h1
  rw [jv_ordX, w.jOrd_of_lt_crit hμ] at h2
  ext y
  constructor
  · intro hy
    rw [h2] at hy
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (mem_inter.mp hy).2
    have hfix := w.jOrd_of_lt_crit (hξ.trans hμ)
    exact (w.ord_mem_iff (hξ.trans hμlam) x).mpr (by rw [hfix]; exact (mem_inter.mp hy).1)
  · intro hy
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hx hy)
    have hfix := w.jOrd_of_lt_crit (hξ.trans hμ)
    have := (w.ord_mem_iff (hξ.trans hμlam) x).mp hy
    rwa [hfix] at this

/-! ### Theorem 3.1(3): the critical points are inaccessible in `A` -/

/-- No function in `A` maps `𝒫^A(μ)` onto the critical point, for `μ < κ`. -/
theorem no_surj_pow_crit (hP : PairClosed A) (hpow : ∀ y ∈ A, powA A y ∈ A)
    (hlim : ∀ a < lam, a + 1 < lam) : SLSemA A (ordZ w.crit) := by
  intro μz hμz hex
  obtain ⟨μ, hμ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hμz
  have hμlam : μ < lam := hμ.trans w.crit_lt
  have hpA : powA A (ordZ μ) ∈ A := hpow _ (w.ord_mem_A hμlam)
  have hpV : powA A (ordZ μ) ∈ V_ lam :=
    subset_mem_V (fun t ht => mem_powerset.mpr (mem_powA.mp ht).2)
      (powerset_mem_V hlim (ordZ_mem_V hμlam))
  let pX : Str w.X Y := ⟨powA A (ordZ μ), w.base _ hpA hpV⟩
  let kX : Str w.X Y := w.ordX w.crit w.crit_lt
  obtain ⟨fX, hsX⟩ := w.surj_in_X hP pX kX hex
  have hsJ := (w.surj_iff hP fX pX kX).mp hsX
  have hpJ : w.jv pX = powA A (ordZ μ) := by
    have := (w.pow_iff pX (w.ordX μ hμlam)).mp rfl
    rwa [jv_ordX, w.jOrd_of_lt_crit hμ] at this
  have hkJ : w.jv kX = ordZ (w.jOrd w.crit) := w.jv_ordX w.crit_lt
  rw [hpJ, hkJ] at hsJ
  obtain ⟨u, hu, hp⟩ := hsJ.2.2 (ordZ w.crit)
    (Ordinal.toZFSet_mem_toZFSet_iff.mpr w.crit_lt_jOrd)
  have hsX' : SurjSem A fX.1 (powA A (ordZ μ)) (ordZ w.crit) := hsX
  obtain ⟨v, hv, hp'⟩ := hsX'.1 u hu
  obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hv
  have huA : u ∈ A := (mem_powA.mp hu).1
  let uX : Str w.X Y := ⟨u, w.mem_X_of_subset_ord huA hμlam (mem_powA.mp hu).2⟩
  have hζlam : ζ < lam := hζ.trans w.crit_lt
  have hp'' := (w.pair_mem_iff hP uX (w.ordX ζ hζlam) fX).mp hp'
  rw [w.jv_subset_fixed uX hμ (mem_powA.mp hu).2, jv_ordX, w.jOrd_of_lt_crit hζ] at hp''
  have heq : ordZ w.crit = ordZ ζ :=
    hsJ.2.1 u huA (ordZ w.crit) (w.ord_mem_A w.crit_lt) (ordZ ζ) (w.ord_mem_A hζlam) hp hp''
  exact absurd (ordZ_inj heq) (ne_of_gt hζ)

/-- The same for every point of the critical sequence, by elementarity. -/
theorem slSem_critSeq (hP : PairClosed A) (hpow : ∀ y ∈ A, powA A y ∈ A)
    (hlim : ∀ a < lam, a + 1 < lam) (n : ℕ) : SLSemA A (ordZ (w.critSeq n)) := by
  induction n with
  | zero => exact w.no_surj_pow_crit hP hpow hlim
  | succ n ih =>
    have h := (w.sl_iff hP hpow (w.ordX _ (w.critSeq_lt n))).mp ih
    rw [jv_ordX] at h
    rw [critSeq_succ]
    exact h

/-- **The critical point is regular in `A`.** -/
theorem crit_regular (hP : PairClosed A) {μ : Ordinal.{u}} (hμ : μ < w.crit)
    (S : ZFSet.{u}) (hSA : S ∈ A) (hS : S ⊆ ordZ w.crit) (hcof : CofSem S (ordZ w.crit)) :
    ¬ ∃ f ∈ A, SurjSem A f (ordZ μ) S := by
  intro hex
  have hμlam : μ < lam := hμ.trans w.crit_lt
  let sX : Str w.X Y := ⟨S, w.mem_X_of_subset_ord hSA w.crit_lt hS⟩
  let kX : Str w.X Y := w.ordX w.crit w.crit_lt
  obtain ⟨fX, hsX⟩ := w.surj_in_X hP (w.ordX μ hμlam) sX hex
  have hsJ := (w.surj_iff hP fX (w.ordX μ hμlam) sX).mp hsX
  rw [jv_ordX, w.jOrd_of_lt_crit hμ] at hsJ
  have hsX' : SurjSem A fX.1 (ordZ μ) S := hsX
  have hjS : w.jv sX ⊆ S := by
    intro v hv
    obtain ⟨u, hu, hp⟩ := hsJ.2.2 v hv
    obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hu
    obtain ⟨v', hv', hp'⟩ := hsX'.1 _ hu
    obtain ⟨η, hη, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS hv')
    have hζlam : ζ < lam := hζ.trans hμlam
    have hηlam : η < lam := hη.trans w.crit_lt
    have hp'' := (w.pair_mem_iff hP (w.ordX ζ hζlam) (w.ordX η hηlam) fX).mp hp'
    rw [jv_ordX, jv_ordX, w.jOrd_of_lt_crit (hζ.trans hμ), w.jOrd_of_lt_crit hη] at hp''
    have hvA : v ∈ A := w.trans.subset_of_mem (w.j sX).2 hv
    have : v = ordZ η :=
      hsJ.2.1 (ordZ ζ) (w.ord_mem_A hζlam) v hvA (ordZ η) (w.ord_mem_A hηlam) hp hp''
    rw [this]
    exact hv'
  have hcofJ := (w.cof_iff sX kX).mp hcof
  have hkJ : w.jv kX = ordZ (w.jOrd w.crit) := w.jv_ordX w.crit_lt
  rw [hkJ] at hcofJ
  obtain ⟨s, hs, hor⟩ := hcofJ (ordZ w.crit) (Ordinal.toZFSet_mem_toZFSet_iff.mpr w.crit_lt_jOrd)
  obtain ⟨η, hη, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS (hjS hs))
  rcases hor with h1 | h1
  · exact lt_asymm hη (Ordinal.toZFSet_mem_toZFSet_iff.mp h1)
  · exact absurd (ordZ_inj h1) (ne_of_gt hη)

/-! ### Theorem 5.1(2): fixed small sets, for witnesses of cofinal type -/

/-- The least ordinal that `A` maps onto a fixed `S` is fixed by `j`. -/
theorem least_surj_fixed (hP : PairClosed A) (S : Str w.X Y) (hfix : w.jv S = S.1)
    (μ : Ordinal.{u}) (hμ : μ < lam) (hμs : ∃ f ∈ A, SurjSem A f (ordZ μ) S.1)
    (hmin : ∀ ν, ν < μ → ¬ ∃ f ∈ A, SurjSem A f (ordZ ν) S.1) : w.jOrd μ = μ := by
  have hA := w.trans
  have hμA : ordZ μ ∈ A := w.ord_mem_A hμ
  have hpar : ∀ k, w.j (scons w.lamX (fun _ => S) k) = w.up (scons w.lamX (fun _ => S) k) := by
    intro k
    cases k with
    | zero => exact Subtype.ext w.j_lam
    | succ k => exact Subtype.ext hfix
  have hx : Sat (memOn A)
      (scons ⟨ordZ μ, hμA⟩ (fun k => w.up (scons w.lamX (fun _ => S) k))) minSurjF := by
    refine (minSurjF_spec hA hP _).mpr
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr hμ, hμs, fun ν hν => ?_⟩
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hν
    exact hmin ξ hξ
  have huniq : ∀ y, Sat (memOn A)
      (scons y (fun k => w.up (scons w.lamX (fun _ => S) k))) minSurjF → y = ⟨ordZ μ, hμA⟩ := by
    intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := (minSurjF_spec hA hP _).mp hy
    have hy1' : y.1 ∈ ordZ lam := hy1
    have hy2' : ∃ f ∈ A, SurjSem A f y.1 S.1 := hy2
    have hy3' : ∀ ν ∈ y.1, ¬ ∃ f ∈ A, SurjSem A f ν S.1 := hy3
    obtain ⟨ξ, hξ, hyξ⟩ := Ordinal.mem_toZFSet_iff.mp hy1'
    have hyξ' : y.1 = ordZ ξ := by
      first
        | exact hyξ
        | exact hyξ.symm
    apply Subtype.ext
    show y.1 = ordZ μ
    rw [hyξ'] at hy2' hy3' ⊢
    rcases lt_trichotomy ξ μ with h | h | h
    · exact absurd hy2' (hmin ξ h)
    · rw [h]
    · exact absurd hμs (hy3' (ordZ μ) (Ordinal.toZFSet_mem_toZFSet_iff.mpr h))
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed minSurjF _ hpar ⟨ordZ μ, hμA⟩ hx huniq
  have hd0 : (w.up d).1 = ordZ μ := congrArg Subtype.val hd
  have hd1 : d = w.ordX μ hμ := Subtype.ext hd0
  have hjd1 : w.jv d = ordZ μ := congrArg Subtype.val hjd
  rw [hd1, jv_ordX] at hjd1
  exact ordZ_inj hjd1

/-- **Fixed small sets (note, Theorem 5.1(2); synthesis Lemma 8.4(a)).**  For a witness of
cofinal type, a fixed `S ∈ X`, `S ⊆ lam`, that is the image of an ordinal below `lam` under
a function of `A`, lies below the critical point. -/
theorem fixed_small_subset (hcof : w.CofinalType) (hP : PairClosed A) (S : Str w.X Y)
    (hS : S.1 ⊆ ordZ lam) (hfix : w.jv S = S.1)
    (hsmall : ∃ μ, μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) S.1) : S.1 ⊆ ordZ w.crit := by
  obtain ⟨μ, hμP, hmin⟩ : ∃ μ, (μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) S.1) ∧
      ∀ ν, ν < μ → ¬ ∃ f ∈ A, SurjSem A f (ordZ ν) S.1 := by
    let P : Set Ordinal.{u} := {μ | μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) S.1}
    have hPne : P.Nonempty := hsmall
    refine ⟨wellFounded_lt.min P hPne, wellFounded_lt.min_mem P hPne, fun ν hν hf => ?_⟩
    have hνP : ν ∈ P := ⟨hν.trans (wellFounded_lt.min_mem P hPne).1, hf⟩
    exact wellFounded_lt.not_lt_min P hνP hν
  have hμ : μ < lam := hμP.1
  have hfixed : w.jOrd μ = μ := w.least_surj_fixed hP S hfix μ hμ hμP.2 hmin
  have hμκ : μ < w.crit := (w.fixed_iff_lt_crit hcof hμ).mp hfixed
  obtain ⟨fX, hsX⟩ := w.surj_in_X hP (w.ordX μ hμ) S hμP.2
  have hsJ : SurjSem A (w.jv fX) (ordZ μ) S.1 := by
    have h3 := (w.surj_iff hP fX (w.ordX μ hμ) S).mp hsX
    rwa [jv_ordX, hfixed, hfix] at h3
  have hsX' : SurjSem A fX.1 (ordZ μ) S.1 := hsX
  let Sset : Set Ordinal.{u} := {ξ | ordZ ξ ∈ S.1}
  have hSlt : ∀ ξ ∈ Sset, ξ < lam := fun ξ hξ => Ordinal.toZFSet_mem_toZFSet_iff.mp (hS hξ)
  have himage : w.jOrd '' Sset = Sset := by
    apply Set.Subset.antisymm
    · rintro _ ⟨ξ, hξ, rfl⟩
      have := (w.ord_mem_iff (hSlt ξ hξ) S).mp hξ
      rwa [hfix] at this
    · intro η hη
      obtain ⟨u, hu, hp⟩ := hsJ.2.2 (ordZ η) hη
      obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hu
      obtain ⟨v', hv', hp'⟩ := hsX'.1 _ hu
      obtain ⟨η', hη', rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS hv')
      have hζlam : ζ < lam := hζ.trans hμ
      have hp'' := (w.pair_mem_iff hP (w.ordX ζ hζlam) (w.ordX η' hη') fX).mp hp'
      rw [jv_ordX, jv_ordX, w.jOrd_of_lt_crit (hζ.trans hμκ)] at hp''
      have heq : ordZ η = ordZ (w.jOrd η') :=
        hsJ.2.1 (ordZ ζ) (w.ord_mem_A hζlam) (ordZ η) (w.ord_mem_A (hSlt η hη))
          (ordZ (w.jOrd η')) (w.ord_mem_A (w.jOrd_lt hη')) hp hp''
      exact ⟨η', hv', (ordZ_inj heq).symm⟩
  have hbelow := SecondRound.fixed_small_set_below_crit w.jOrd lam w.crit
    (fun a b hab hb => w.jOrd_strictMono hab hb) (fun ξ h1 h2 => w.moved hcof h1 h2)
    Sset hSlt himage
  intro x hx
  obtain ⟨ξ, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS hx)
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hbelow ξ hx)

/-- **No small fixed family (note, Theorem 5.1(2); synthesis Lemma 8.4(b)).**  For a witness
of cofinal type there is no nonempty fixed `F ∈ X` of cofinal subsets of `lam` whose union
belongs to `A` and is internally small. -/
theorem no_small_fixed_family (hcof : w.CofinalType) (hP : PairClosed A) (F : Str w.X Y)
    (hfix : w.jv F = F.1) (hmem : ∀ b ∈ F.1, CofinalIn b lam) (hUA : ⋃₀ F.1 ∈ A)
    (hsmall : ∃ μ, μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) (⋃₀ F.1)) : F.1 = ∅ := by
  by_contra hne
  obtain ⟨b, hb⟩ := (ZFSet.eq_empty_or_nonempty F.1).resolve_left hne
  have husub : (⋃₀ F.1 : ZFSet.{u}) ⊆ ordZ lam := by
    intro t ht
    obtain ⟨b', hb', htb'⟩ := mem_sUnion.mp ht
    exact subOrd_iff_subset.mp (hmem b' hb').1 htb'
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed (sUnionF 0 1) (fun _ => F)
    (fun _ => Subtype.ext hfix) ⟨⋃₀ F.1, hUA⟩
    ((sUnionF_spec w.trans _ 0 1).mpr rfl)
    (fun y hy => Subtype.ext ((sUnionF_spec w.trans _ 0 1).mp hy))
  have hd1 : d.1 = ⋃₀ F.1 := congrArg Subtype.val hd
  have hjd1 : w.jv d = d.1 := (congrArg Subtype.val hjd).trans hd1.symm
  have hsmall' : ∃ μ, μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) d.1 := by rw [hd1]; exact hsmall
  have hsub := w.fixed_small_subset hcof hP d (by rw [hd1]; exact husub) hjd1 hsmall'
  obtain ⟨η, hκη, -, hηb⟩ := (hmem b hb).2 w.crit w.crit_lt
  have : ordZ η ∈ ordZ w.crit := hsub (by rw [hd1]; exact mem_sUnion.mpr ⟨b, hb, hηb⟩)
  exact absurd (Ordinal.toZFSet_mem_toZFSet_iff.mp this) (not_lt.mpr hκη)

/-- **No small definable family (note, Theorem 5.1(3), definable form).**  If a family of
cofinal subsets of `lam` with internally small union is the unique solution in `A` of a
formula whose parameters are fixed by `j`, it is empty.  (The reduction of ordinal
definability from parameters in `V_lam` to this case is the least-counterexample argument of
the note, which needs a satisfaction predicate inside `A` and is not formalized.) -/
theorem no_small_definable_family (hcof : w.CofinalType) (hP : PairClosed A)
    (φ : Form) (e : ℕ → Str w.X Y) (hpar : ∀ k, w.j (e k) = w.up (e k)) (F : Carrier A)
    (hF : Sat (memOn A) (scons F (fun k => w.up (e k))) φ)
    (huniq : ∀ y, Sat (memOn A) (scons y (fun k => w.up (e k))) φ → y = F)
    (hmem : ∀ b ∈ F.1, CofinalIn b lam) (hUA : ⋃₀ F.1 ∈ A)
    (hsmall : ∃ μ, μ < lam ∧ ∃ f ∈ A, SurjSem A f (ordZ μ) (⋃₀ F.1)) : F.1 = ∅ := by
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed φ e hpar F hF huniq
  have hd1 : d.1 = F.1 := congrArg Subtype.val hd
  have hjd1 : w.jv d = d.1 := (congrArg Subtype.val hjd).trans hd1.symm
  rw [← hd1] at hmem hUA hsmall ⊢
  exact w.no_small_fixed_family hcof hP d hjd1 hmem hUA hsmall

end TWitness

end Cardinals
