import DiophantineConsistency.ModelRepArith
import DiophantineConsistency.ModelBetaFunction
import DiophantineConsistency.ArithmeticPellResidueClasses
import DiophantineConsistency.ArithmeticPellIndexDivisibility
import DiophantineConsistency.ArithmeticPellSquaredSeed

/-! # Internal correctness of the Pell-coordinate representation

`PellRepresentation.rep` represents `x = xₙ(a) ∧ y = yₙ(a)` by Matiyasevich's
finite certificate (Mathlib's `Pell.matiyasevic`). Inside every model `V` of
`𝗜𝚺₁` we prove that the same syntax is correct for the internal Pell sequence of
`ArithmeticPellRecurrence` with base `a = c + 2`:

* `holds_normRep`, `holds_finiteRep`, `holds_criterionRep`: the syntax evaluates
  to the internal certificate (`INorm` is the norm equation in `DiffRing V`);
* `matiyasevic`: the internal certificate holds exactly for internal Pell
  coordinates. Soundness uses the internal classification
  (`ArithmeticPellClassification.solution_index`), index divisibility
  (`ArithmeticPellIndexDivisibility.ordinate_divides_index`), the residue
  classes of the first coordinate (`ArithmeticPellResidueClasses.x_residue_classes`),
  the base-change congruence `base_change` proved here, and the ordinate
  congruence `ArithmeticPellCongruences.residue_mod`. Completeness takes the
  auxiliary index `2·n·yₙ` (`ArithmeticPellSquaredSeed.squared_ordinate`) and an
  auxiliary base chosen by a Bezout identity in `DiffRing V`;
* `holds_pellRep`: the final interface. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace DiophantineConsistency.ModelRepPell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelDifferenceRing ModelScalarPR ModelRepBasic ModelRepArith
open ArithmeticPellRecurrence ArithmeticGcdNormalization
open AdaptiveEquationSyntax2011 (InternalZero)

/-! ### The internal predicates -/

section Predicates
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The norm equation `x² - (a²-1) y² = 1`, evaluated in the ring of differences. -/
def INorm (a x y : V) : Prop :=
  (ι x * ι x - (ι a * ι a - 1) * ι y * ι y : DiffRing V) = 1

/-- The internal Pell graph: `x = xₙ(a)`, `y = yₙ(a)` with `a = (a-2)+2`. -/
def PellGraph (a n x y : V) : Prop :=
  1 < a ∧ x = xcoord n (a - 2) ∧ y = ycoord n (a - 2)

/-- The finite Matiyasevich certificate, in the raw form of the syntax. -/
def FinRawV (a n x y u w s t B : V) : Prop :=
  INorm a x y ∧ INorm a u w ∧ INorm B s t ∧ ((1 : ℕ) : V) < B ∧
    B % (((4 : ℕ) : V) * y) = ((1 : ℕ) : V) % (((4 : ℕ) : V) * y) ∧ B % u = a % u ∧
    ((0 : ℕ) : V) < w ∧ y * y ∣ w ∧ s % u = x % u ∧
    t % (((4 : ℕ) : V) * y) = n % (((4 : ℕ) : V) * y)

/-- The finite Matiyasevich certificate. -/
def FinCrit (a n x y u w s t B : V) : Prop :=
  INorm a x y ∧ INorm a u w ∧ INorm B s t ∧ 1 < B ∧ B % (4 * y) = 1 % (4 * y) ∧
    B % u = a % u ∧ 0 < w ∧ y * y ∣ w ∧ s % u = x % u ∧ t % (4 * y) = n % (4 * y)

/-- The whole criterion, in the raw form of the syntax. -/
def CritRaw (a n x y : V) : Prop :=
  ((1 : ℕ) : V) < a ∧ n ≤ y ∧ ((x = ((1 : ℕ) : V) ∧ y = ((0 : ℕ) : V)) ∨
    ∃ z : Fin 5 → V, FinRawV a n x y (z 0) (z 1) (z 2) (z 3) (z 4))

/-- The whole criterion. -/
def Crit (a n x y : V) : Prop :=
  1 < a ∧ n ≤ y ∧ ((x = 1 ∧ y = 0) ∨ ∃ u w s t B : V, FinCrit a n x y u w s t B)

theorem finRaw_iff (a n x y u w s t B : V) :
    FinRawV a n x y u w s t B ↔ FinCrit a n x y u w s t B := by
  have h4 : ((4 : ℕ) : V) = 4 := Nat.cast_ofNat
  unfold FinRawV FinCrit
  simp only [h4, Nat.cast_one, Nat.cast_zero]

theorem critRaw_iff (a n x y : V) : CritRaw a n x y ↔ Crit a n x y := by
  unfold CritRaw Crit
  simp only [Nat.cast_one, Nat.cast_zero, finRaw_iff]
  constructor
  · rintro ⟨h1, h2, h3 | ⟨z, hz⟩⟩
    · exact ⟨h1, h2, Or.inl h3⟩
    · exact ⟨h1, h2, Or.inr ⟨z 0, z 1, z 2, z 3, z 4, hz⟩⟩
  · rintro ⟨h1, h2, h3 | ⟨u, w, s, t, B, hz⟩⟩
    · exact ⟨h1, h2, Or.inl h3⟩
    · exact ⟨h1, h2, Or.inr ⟨![u, w, s, t, B], hz⟩⟩

/-- The norm in the ring of differences is the toolkit's natural norm. -/
theorem inorm_iff (c x y : V) : INorm (c + 2) x y ↔ x * x = 1 + delta c * y * y := by
  have h2 : (ι (2 : V) : DiffRing V) = 2 := map_ofNat ι 2
  have h3 : (ι (3 : V) : DiffRing V) = 3 := map_ofNat ι 3
  have hc2 : (ι (c + 2) : DiffRing V) = ι c + 2 := by rw [map_add, h2]
  have hd : (ι (delta c) : DiffRing V) = (ι c + 1) * (ι c + 3) := by
    rw [delta, map_mul, map_add, map_add, map_one, h3]
  have key : x * x = 1 + delta c * y * y ↔
      (ι (x * x) : DiffRing V) = ι (1 + delta c * y * y) := ι_injective.eq_iff.symm
  rw [key, map_mul, map_add, map_mul, map_mul, map_one, hd]
  unfold INorm
  rw [hc2]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end Predicates

/-! ### The syntax evaluates to the internal criterion -/

section Syntax

theorem residual_one {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {σ : Type*}
    (u : σ → V) : residual (1 : Expr σ) u = 1 :=
  (residual_ofNat 1 u).trans Nat.cast_one

theorem holds_normRep {σ : Type*} (a x y : σ) :
    Holds (PellRepresentation.normRep a x y) (fun V _ _ v => INorm (v a) (v x) (v y)) := by
  refine holds_congr _ ?_ (holds_equality
    (Expr.var x * Expr.var x - (Expr.var a * Expr.var a - 1) * Expr.var y * Expr.var y)
    (1 : Expr σ))
  intro V _ _ v
  change ι (v x) * ι (v x) - (ι (v a) * ι (v a) - residual (1 : Expr σ) v) * ι (v y) * ι (v y) =
      residual (1 : Expr σ) v ↔ INorm (v a) (v x) (v y)
  rw [residual_one]
  exact Iff.rfl

/-- The certificate variables `a,n,x,y | u,w,s,t,b`. -/
abbrev PV := PellRepresentation.CertificateVar

theorem holds_finiteRep : Holds PellRepresentation.finiteRep (fun V _ _ q =>
    FinRawV (q (Sum.inl 0)) (q (Sum.inl 1)) (q (Sum.inl 2)) (q (Sum.inl 3)) (q (Sum.inr 0))
      (q (Sum.inr 1)) (q (Sum.inr 2)) (q (Sum.inr 3)) (q (Sum.inr 4))) :=
  holds_congr _ (by intro V _ _ q; exact Iff.rfl)
    (holds_conjunction (holds_normRep (Sum.inl 0 : PV) (Sum.inl 2) (Sum.inl 3))
    (holds_conjunction (holds_normRep (Sum.inl 0 : PV) (Sum.inr 0) (Sum.inr 1))
    (holds_conjunction (holds_normRep (Sum.inr 4 : PV) (Sum.inr 2) (Sum.inr 3))
    (holds_conjunction (holds_naturalLt (1 : NatExpr PV) (NatExpr.var (Sum.inr 4)))
    (holds_conjunction (holds_naturalModEq (NatExpr.var (Sum.inr 4 : PV)) 1 (4 * NatExpr.var (Sum.inl 3)))
    (holds_conjunction
      (holds_naturalModEq (NatExpr.var (Sum.inr 4 : PV)) (NatExpr.var (Sum.inl 0)) (NatExpr.var (Sum.inr 0)))
    (holds_conjunction (holds_naturalLt (0 : NatExpr PV) (NatExpr.var (Sum.inr 1)))
    (holds_conjunction
      (holds_naturalDvd (NatExpr.var (Sum.inl 3 : PV) * NatExpr.var (Sum.inl 3)) (NatExpr.var (Sum.inr 1)))
    (holds_conjunction
      (holds_naturalModEq (NatExpr.var (Sum.inr 2 : PV)) (NatExpr.var (Sum.inl 2)) (NatExpr.var (Sum.inr 0)))
      (holds_naturalModEq (NatExpr.var (Sum.inr 3 : PV)) (NatExpr.var (Sum.inl 1))
        (4 * NatExpr.var (Sum.inl 3))))))))))))

theorem holds_criterionRep : Holds PellRepresentation.criterionRep
    (fun V _ _ v => CritRaw (v 0) (v 1) (v 2) (v 3)) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_conjunction (holds_naturalLt (1 : NatExpr (Fin 4)) (NatExpr.var 0))
      (holds_conjunction (holds_naturalLe (NatExpr.var (1 : Fin 4)) (NatExpr.var 3))
        (holds_disjunction
          (holds_conjunction (holds_naturalEquality (NatExpr.var (2 : Fin 4)) 1)
            (holds_naturalEquality (NatExpr.var (3 : Fin 4)) 0))
          (holds_existsBlock holds_finiteRep))))

end Syntax

/-! ### Modular arithmetic helpers -/

section Helpers
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_congr_add {a b a' b' m : V} (hm : 0 < m) (ha : a % m = a' % m)
    (hb : b % m = b' % m) : (a + b) % m = (a' + b') % m := by
  rw [mod_add hm, ha, hb, ← mod_add hm]

theorem mod_congr_mul {a b a' b' m : V} (hm : 0 < m) (ha : a % m = a' % m)
    (hb : b % m = b' % m) : (a * b) % m = (a' * b') % m := by
  rw [mod_mul hm, ha, hb, ← mod_mul hm]

/-- If `c+2 ≡ 1 (mod m)`, then `m ∣ c+1`. -/
theorem dvd_of_mod_two {c m : V} (hm : 0 < m) (h : (c + 2) % m = 1 % m) : m ∣ c + 1 := by
  apply mod_eq_zero_iff_dvd.mp
  have h' := ArithmeticPellResidueClasses.mod_add_cancel (c + 1) 0 1 m hm
    (by rw [show c + 1 + 1 = c + 2 by ring, zero_add, h])
  rw [LO.FirstOrder.Arithmetic.zero_mod] at h'
  exact h'

theorem lt_four_mul {y : V} (hy : 0 < y) : y < 4 * y :=
  calc y < y + 3 * y := lt_add_of_pos_right _ (mul_pos (by simp) hy)
    _ = 4 * y := by ring

theorem two_lt_four_mul {y : V} (hy : 0 < y) : y + y < 4 * y :=
  calc y + y < y + y + (y + y) := lt_add_of_pos_right _ (add_pos hy hy)
    _ = 4 * y := by ring

theorem one_lt_add_two (c : V) : 1 < c + 2 :=
  LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mpr le_add_self

/-- Changing the base modulo `m` changes both Pell coordinates only modulo `m`. -/
theorem base_change (c c' m : V) (hm : 0 < m) (h : (c + 2) % m = (c' + 2) % m) (k : V) :
    xcoord k c % m = xcoord k c' % m ∧ ycoord k c % m = ycoord k c' % m := by
  have hd : delta c % m = delta c' % m := by
    apply ArithmeticPellResidueClasses.mod_add_cancel _ _ 1 m hm
    rw [show delta c + 1 = (c + 2) * (c + 2) by unfold delta; ring,
      show delta c' + 1 = (c' + 2) * (c' + 2) by unfold delta; ring]
    exact mod_congr_mul hm h h
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [x_succ, x_succ, y_succ, y_succ]
    exact ⟨mod_congr_add hm (mod_congr_mul hm h ih.1) (mod_congr_mul hm hd ih.2),
      mod_congr_add hm ih.1 (mod_congr_mul hm h ih.2)⟩

/-- An auxiliary base `B > 1` with `B ≡ 1 (mod 4y)` and `B ≡ a (mod u)`. -/
theorem exists_aux_base (y u a : V) (hy : 0 < y) (hu : 0 < u) (hcop : Bez (4 * y) u 1) :
    ∃ B : V, 1 < B ∧ B % (4 * y) = 1 % (4 * y) ∧ B % u = a % u := by
  obtain ⟨α, β, hαβ⟩ := (ModelBetaFunction.bez_one_iff_ring (a := 4 * y) (b := u)).mp hcop
  obtain ⟨K, hK⟩ := nonneg_iff.mp (abs_nonneg (ι u * β + ι a * (ι (4 * y) * α)))
  have h4pos : (0 : V) < 4 * y := mul_pos (by simp) hy
  have h4 : (1 : DiffRing V) ≤ ι (4 * y) :=
    calc (1 : DiffRing V) = ι 1 := (map_one (ι (V := V))).symm
      _ ≤ ι (4 * y) := ι_le_ι.mpr (pos_iff_one_le.mp h4pos)
  have hu1 : (1 : DiffRing V) ≤ ι u :=
    calc (1 : DiffRing V) = ι 1 := (map_one (ι (V := V))).symm
      _ ≤ ι u := ι_le_ι.mpr (pos_iff_one_le.mp hu)
  have hK0 : (0 : DiffRing V) ≤ ι K := ι_nonneg K
  have hprod : ι K + 2 ≤ ι (4 * y) * ι u * (ι K + 2) :=
    le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le h4 hu1)
  have habs : -(ι u * β + ι a * (ι (4 * y) * α)) ≤ ι K := by
    rw [← hK]
    exact neg_le_abs _
  obtain ⟨B, hB⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤
      ι u * β + ι a * (ι (4 * y) * α) + ι (4 * y) * ι u * (ι K + 2) by linarith)
  refine ⟨B, ?_, ?_, ?_⟩
  · have h2 : (2 : DiffRing V) ≤ ι B := by
      rw [← hB]
      linarith
    exact LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mpr (ModelArithmetic.two_le_of_ι h2)
  · apply ModelBetaFunction.mod_eq_of_sub_eq (q := α * (ι a - 1) + ι u * (ι K + 2))
    rw [← hB, map_one]
    linear_combination hαβ
  · apply ModelBetaFunction.mod_eq_of_sub_eq (q := β * (1 - ι a) + ι (4 * y) * (ι K + 2))
    rw [← hB]
    linear_combination (ι a) * hαβ

end Helpers

/-! ### Matiyasevich's criterion inside the model -/

section Matiyasevich
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Completeness: internal Pell coordinates satisfy the certificate. -/
theorem crit_of_pell (c n : V) : Crit (c + 2) n (xcoord n c) (ycoord n c) := by
  refine ⟨one_lt_add_two c, time_le_y n c, ?_⟩
  rcases eq_zero_or_pos n with hn | hn
  · left
    subst hn
    simp
  right
  obtain ⟨y, hyd⟩ : ∃ y, ycoord n c = y := ⟨_, rfl⟩
  obtain ⟨x, hxd⟩ : ∃ x, xcoord n c = x := ⟨_, rfl⟩
  have hnorm : x * x = 1 + delta c * y * y := by
    rw [← hxd, ← hyd]
    exact ArithmeticPellRecurrence.norm n c
  have hy : 0 < y := by
    rw [← hyd]
    exact lt_of_lt_of_le hn (time_le_y n c)
  obtain ⟨i, hi⟩ := ArithmeticPellSquaredSeed.squared_ordinate n c
  rw [hyd] at hi
  rw [hxd, hyd]
  have hyw : y * y ∣ ycoord (2 * (n * y)) c := by
    have h1 : y * y ∣ ycoord (n * y) c := ⟨i, by rw [hi]; ring⟩
    exact dvd_trans h1
      ((ArithmeticPellStrongDivisibility.y_dvd_iff c (n * y) (2 * (n * y))).mpr
        (dvd_mul_left _ 2))
  have hm : 0 < 2 * (n * y) := mul_pos (by simp) (mul_pos hn hy)
  have hw : 0 < ycoord (2 * (n * y)) c := lt_of_lt_of_le hm (time_le_y _ c)
  have hu : 0 < xcoord (2 * (n * y)) c := lt_of_lt_of_le (by simp) (one_le_x _ c)
  have hbez_y : Bez y (xcoord (2 * (n * y)) c) 1 := by
    obtain ⟨q, hq⟩ := dvd_trans (dvd_mul_right y y) hyw
    refine ⟨delta c * q * ycoord (2 * (n * y)) c, 0, 0, xcoord (2 * (n * y)) c, ?_⟩
    rw [ArithmeticPellRecurrence.norm (2 * (n * y)) c, hq]
    ring
  have hbez_2 : Bez 2 (xcoord (2 * (n * y)) c) 1 := by
    refine ⟨delta c * ycoord (n * y) c * ycoord (n * y) c, 0, 0, 1, ?_⟩
    rw [ArithmeticPellPeriodicity.double_x (n * y) c]
    ring
  have hbez : Bez (4 * y) (xcoord (2 * (n * y)) c) 1 := by
    have h := ModelBetaFunction.bez_mul (ModelBetaFunction.bez_mul hbez_2 hbez_2) hbez_y
    rwa [show (2 : V) * 2 * y = 4 * y by ring] at h
  obtain ⟨B, hB1, hB4, hBu⟩ := exists_aux_base y (xcoord (2 * (n * y)) c) (c + 2) hy hu hbez
  have hB2 : 2 ≤ B := LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mp hB1
  obtain ⟨c', hc'⟩ : ∃ c', B = c' + 2 := ⟨B - 2, (tsub_add_cancel_of_le hB2).symm⟩
  have h4pos : 0 < 4 * y := mul_pos (by simp) hy
  have h4y : 4 * y ∣ c' + 1 := dvd_of_mod_two h4pos (by rw [← hc']; exact hB4)
  refine ⟨xcoord (2 * (n * y)) c, ycoord (2 * (n * y)) c, xcoord n c', ycoord n c', B,
    (inorm_iff c x y).mpr hnorm, (inorm_iff c _ _).mpr (ArithmeticPellRecurrence.norm _ c),
    ?_, hB1, hB4, hBu, hw, hyw, ?_, ?_⟩
  · rw [hc']
    exact (inorm_iff c' _ _).mpr (ArithmeticPellRecurrence.norm n c')
  · have h := (base_change c' c (xcoord (2 * (n * y)) c) hu (by rw [← hc']; exact hBu) n).1
    rw [h, hxd]
  · exact (ArithmeticPellCongruences.residue_mod n c' (4 * y) h4y h4pos).2

/-- Soundness: the certificate forces the internal Pell coordinates. -/
theorem pell_of_crit (c n x y : V) (h : Crit (c + 2) n x y) :
    x = xcoord n c ∧ y = ycoord n c := by
  obtain ⟨_, hny, ⟨hx1, hy0⟩ | ⟨u, w, s, t, B, hxy, huw, hst, hB1, hB4, hBu, hw, hyw, hsx, htn⟩⟩ :=
    h
  · subst hx1 hy0
    have hn0 : n = 0 := nonpos_iff_eq_zero.mp hny
    subst hn0
    simp
  have hxy' := (inorm_iff c x y).mp hxy
  have huw' := (inorm_iff c u w).mp huw
  have hB2 : 2 ≤ B := LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mp hB1
  obtain ⟨c', hc'⟩ : ∃ c', B = c' + 2 := ⟨B - 2, (tsub_add_cancel_of_le hB2).symm⟩
  subst hc'
  have hst' := (inorm_iff c' s t).mp hst
  obtain ⟨i, -, hxi, hyi⟩ := ArithmeticPellClassification.solution_index c x y hxy'
  obtain ⟨j, -, hxj, hyj⟩ := ArithmeticPellClassification.solution_index c u w huw'
  obtain ⟨k, -, hxk, hyk⟩ := ArithmeticPellClassification.solution_index c' s t hst'
  have hy : 0 < y := by
    rcases eq_zero_or_pos y with h0 | h0
    · exfalso
      rw [h0, zero_mul, zero_dvd_iff] at hyw
      exact hw.ne' hyw
    · exact h0
  have hi : 0 < i := by
    rcases eq_zero_or_pos i with h0 | h0
    · exfalso
      rw [h0, y_zero] at hyi
      exact hy.ne' hyi.symm
    · exact h0
  have hj : 0 < j := by
    rcases eq_zero_or_pos j with h0 | h0
    · exfalso
      rw [h0, y_zero] at hyj
      exact hw.ne' hyj.symm
    · exact h0
  have hyw' : ycoord i c * ycoord i c ∣ ycoord j c := by
    rw [hyi, hyj]
    exact hyw
  have hij : i ∣ j :=
    (ArithmeticPellStrongDivisibility.y_dvd_iff c i j).mp (dvd_trans (dvd_mul_right _ _) hyw')
  have hyj_dvd : y ∣ j := by
    have h1 := ArithmeticPellIndexDivisibility.ordinate_divides_index c i j hij
      (Dvd.dvd.mul_left hyw' (delta c))
    rwa [hyi] at h1
  have hyle : y ≤ j := LO.FirstOrder.Arithmetic.le_of_dvd hj hyj_dvd
  have hiy : i ≤ y := by
    rw [← hyi]
    exact time_le_y i c
  have hile : i ≤ j := le_trans hiy hyle
  have hu0 : 0 < u := by
    rw [← hxj]
    exact lt_of_lt_of_le (by simp) (one_le_x j c)
  have hkres : xcoord k c % xcoord j c = xcoord i c % xcoord j c := by
    have hbc := (base_change c' c u hu0 hBu k).1
    rw [hxj, hxi, ← hbc, hxk]
    exact hsx
  have hcls := ArithmeticPellResidueClasses.x_residue_classes c i k j hi hile hkres
  have h4y : 0 < 4 * y := mul_pos (by simp) hy
  have h4dvd : 4 * y ∣ 4 * j := mul_dvd_mul_left 4 hyj_dvd
  have h4c : 4 * y ∣ c' + 1 := dvd_of_mod_two h4y hB4
  have hkn : k % (4 * y) = n % (4 * y) := by
    have h1 := (ArithmeticPellCongruences.residue_mod k c' (4 * y) h4c h4y).2
    rw [← h1, hyk]
    exact htn
  have hn4 : n < 4 * y := lt_of_le_of_lt hny (lt_four_mul hy)
  have hi4 : i < 4 * y := lt_of_le_of_lt hiy (lt_four_mul hy)
  have hni : n = i := by
    rcases hcls with hA | hB
    · have h1 : k % (4 * y) = i % (4 * y) := by
        rw [← ArithmeticPellResidueClasses.mod_reduce k (4 * y) (4 * j) h4y h4dvd, hA]
      rw [hkn, mod_eq_self_of_lt hn4, mod_eq_self_of_lt hi4] at h1
      exact h1
    · exfalso
      have h1 : (k + i) % (4 * y) = 0 := by
        rw [← ArithmeticPellResidueClasses.mod_reduce (k + i) (4 * y) (4 * j) h4y h4dvd, hB,
          LO.FirstOrder.Arithmetic.zero_mod]
      rw [ArithmeticPellResidueClasses.mod_add_congr k n i (4 * y) h4y hkn] at h1
      have hlt : n + i < 4 * y := lt_of_le_of_lt (add_le_add hny hiy) (two_lt_four_mul hy)
      rw [mod_eq_self_of_lt hlt] at h1
      exact hi.ne' (add_eq_zero.mp h1).2
  subst hni
  exact ⟨hxi.symm, hyi.symm⟩

/-- Matiyasevich's criterion for the internal Pell coordinates. -/
theorem matiyasevic (a n x y : V) : Crit a n x y ↔ PellGraph a n x y := by
  constructor
  · intro h
    have ha : 1 < a := h.1
    have hac : a - 2 + 2 = a :=
      tsub_add_cancel_of_le (LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mp ha)
    rw [← hac] at h
    obtain ⟨hx, hy⟩ := pell_of_crit (a - 2) n x y h
    exact ⟨ha, hx, hy⟩
  · rintro ⟨ha, hx, hy⟩
    have hac : a - 2 + 2 = a :=
      tsub_add_cancel_of_le (LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mp ha)
    rw [hx, hy]
    have h := crit_of_pell (a - 2) n
    rwa [hac] at h

end Matiyasevich

/-! ### The interface -/

/-- `PellRepresentation.rep` is internally correct for the internal Pell graph. -/
theorem holds_pellRep :
    Holds PellRepresentation.rep (fun V _ _ v => PellGraph (v 0) (v 1) (v 2) (v 3)) := by
  refine holds_congr _ ?_ holds_criterionRep
  intro V _ _ v
  exact (critRaw_iff (v 0) (v 1) (v 2) (v 3)).trans (matiyasevic (v 0) (v 1) (v 2) (v 3))

end DiophantineConsistency.ModelRepPell
