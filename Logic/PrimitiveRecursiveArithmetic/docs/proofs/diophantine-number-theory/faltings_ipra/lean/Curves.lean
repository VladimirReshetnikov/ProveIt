import Std

/-!
Finite arithmetic specifications for a genus-two subproblem of Faltings.
No general finiteness theorem is asserted here. In particular,
`QuinticHeightGoal` is a definition of the missing proposition, not an axiom.
These are ambient Lean definitions and elementary proofs, not objects of
the embedded ConciseIPRA proof calculus.
-/

namespace FaltingsAudit

structure Quintic where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  deriving DecidableEq, Repr

def homogenize (f : Quintic) (u v : Int) : Int :=
  u^5 + f.a4*u^4*v + f.a3*u^3*v^2 + f.a2*u^2*v^3 +
    f.a1*u*v^4 + f.a0*v^5

structure AffineCode where
  u : Int
  v : Nat
  r : Int
  s : Nat
  deriving DecidableEq, Repr

def Canonical (p : AffineCode) : Prop :=
  0 < p.v ∧ 0 < p.s ∧ Nat.gcd p.u.natAbs p.v = 1 ∧
    Nat.gcd p.r.natAbs p.s = 1

instance (p : AffineCode) : Decidable (Canonical p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def AffinePoint (f : Quintic) (p : AffineCode) : Prop :=
  Canonical p ∧ p.r^2 * (p.v : Int)^5 =
    (p.s : Int)^2 * homogenize f p.u (p.v : Int)

instance (f : Quintic) (p : AffineCode) : Decidable (AffinePoint f p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def height (p : AffineCode) : Nat :=
  max (max p.u.natAbs p.v) (max p.r.natAbs p.s)

def shifted (row : List Int) (left right : Nat) : List Int :=
  List.replicate left 0 ++ row ++ List.replicate right 0

def sylvester (f : Quintic) : List (List Int) :=
  let a := [1, f.a4, f.a3, f.a2, f.a1, f.a0]
  let b := [5, 4*f.a4, 3*f.a3, 2*f.a2, f.a1]
  (List.range 4).map (fun j => shifted a j (3-j)) ++
    (List.range 5).map (fun j => shifted b j (4-j))

/-- Laplace expansion with an explicit decreasing dimension. -/
def determinant : Nat → List (List Int) → Int
  | 0, _ => 1
  | _+1, [] => 0
  | n+1, row :: rows =>
      row.zipIdx.foldl (fun acc ej =>
        if ej.1 = 0 then acc else
        acc + (if ej.2 % 2 = 0 then 1 else -1) * ej.1 *
          determinant n (rows.map (fun r => r.eraseIdx ej.2))) 0

def discriminant (f : Quintic) : Int := determinant 9 (sylvester f)

def Good (f : Quintic) : Prop := discriminant f ≠ 0

instance (f : Quintic) : Decidable (Good f) :=
  inferInstanceAs (Decidable (discriminant f ≠ 0))

def HeightBound (f : Quintic) (B : Nat) : Prop :=
  ∀ p, AffinePoint f p → height p ≤ B

/-- OPEN in this package: an explicit positive arithmetic target. -/
def QuinticHeightGoal : Prop :=
  ∀ f, Good f → ∃ B, HeightBound f B

/-- Supplying this structure would require the missing mathematics.
An arbitrary Lean function is not automatically primitive recursive. -/
structure UniformHeightData where
  bound : Quintic → Nat
  correct : ∀ f, Good f → HeightBound f (bound f)

theorem uniformData_implies_goal (d : UniformHeightData) : QuinticHeightGoal := by
  intro f hf
  exact ⟨d.bound f, d.correct f hf⟩

def signedBox (B : Nat) : List Int :=
  (List.range (2*B+1)).map (fun (n : Nat) => (n : Int) - (B : Int))

def positiveBox (B : Nat) : List Nat :=
  (List.range B).map Nat.succ

/-- An explicit order characterization of the absolute-value cutoff. -/
theorem natAbs_le_iff_interval (z : Int) (B : Nat) :
    z.natAbs ≤ B ↔ -(B : Int) ≤ z ∧ z ≤ (B : Int) := by
  constructor
  · intro habs
    have habs' : (z.natAbs : Int) ≤ (B : Int) := Int.ofNat_le.mpr habs
    have hupper : z ≤ (B : Int) := Int.le_trans Int.le_natAbs habs'
    have hneg : -z ≤ (B : Int) := by
      have h := Int.le_natAbs (a := -z)
      rw [Int.natAbs_neg] at h
      exact Int.le_trans h habs'
    have hlower := Int.neg_le_neg hneg
    rw [Int.neg_neg] at hlower
    exact ⟨hlower, hupper⟩
  · rintro ⟨hlower, hupper⟩
    apply Int.ofNat_le.mp
    rcases Int.le_total 0 z with hnonneg | hnonpos
    · rw [Int.natAbs_of_nonneg hnonneg]
      exact hupper
    · rw [Int.ofNat_natAbs_of_nonpos hnonpos]
      have h := Int.neg_le_neg hlower
      rw [Int.neg_neg] at h
      exact h

theorem mem_signedBox (B : Nat) (z : Int) :
    z ∈ signedBox B ↔ z.natAbs ≤ B := by
  simp only [signedBox, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    apply (natAbs_le_iff_interval _ B).mpr
    have hn' : n ≤ B + B := by
      rw [← Nat.two_mul]
      exact Nat.lt_succ_iff.mp hn
    have hnInt : (n : Int) ≤ (B : Int) + (B : Int) := by
      rw [← Int.natCast_add]
      exact Int.ofNat_le.mpr hn'
    constructor
    · have h := Int.add_le_add_right (Int.natCast_nonneg n) (-(B : Int))
      simpa only [Int.zero_add, Int.sub_eq_add_neg] using h
    · exact Int.sub_right_le_iff_le_add.mpr hnInt
  · intro hz
    obtain ⟨hlower, hupper⟩ := (natAbs_le_iff_interval z B).mp hz
    have hnonneg : 0 ≤ z + (B : Int) := by
      have h := Int.add_le_add_right hlower (B : Int)
      simpa only [Int.add_left_neg] using h
    have hcast := Int.toNat_of_nonneg hnonneg
    have hbound : (z + (B : Int)).toNat ≤ 2*B := by
      apply Int.ofNat_le.mp
      rw [hcast, Nat.two_mul, Int.natCast_add]
      exact Int.add_le_add_right hupper (B : Int)
    refine ⟨(z + (B : Int)).toNat, Nat.lt_succ_iff.mpr hbound, ?_⟩
    rw [hcast, Int.add_sub_cancel]

theorem mem_positiveBox (B n : Nat) :
    n ∈ positiveBox B ↔ 0 < n ∧ n ≤ B := by
  simp only [positiveBox, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Nat.succ_pos k, Nat.succ_le_of_lt hk⟩
  · rintro ⟨hpos, hle⟩
    cases n with
    | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
    | succ k => exact ⟨k, Nat.lt_of_succ_le hle, rfl⟩

/-- Complete only up to the supplied component height B. -/
def boundedPoints (f : Quintic) (B : Nat) : List AffineCode :=
  (signedBox B).flatMap fun u =>
    (positiveBox B).flatMap fun v =>
      (signedBox B).flatMap fun r =>
        ((positiveBox B).map (fun s => (⟨u,v,r,s⟩ : AffineCode))).filter
          (fun p => decide (AffinePoint f p))

theorem boundedPoints_spec (f : Quintic) (B : Nat) (p : AffineCode) :
    p ∈ boundedPoints f B ↔ AffinePoint f p ∧ height p ≤ B := by
  cases p with
  | mk u v r s =>
    simp only [boundedPoints, List.mem_flatMap, List.mem_filter, List.mem_map,
      decide_eq_true_eq, AffineCode.mk.injEq, mem_signedBox, mem_positiveBox,
      height, Nat.max_le]
    constructor
    · rintro ⟨a, ha, b, hb, c, hc, ⟨d, hd, hau, hbv, hcr, hds⟩, hp⟩
      subst a
      subst b
      subst c
      subst d
      exact ⟨hp, ⟨ha, hb.2⟩, hc, hd.2⟩
    · rintro ⟨hp, ⟨hu, hv⟩, hr, hs⟩
      exact ⟨u, hu, v, ⟨hp.1.1, hv⟩, r, hr,
        ⟨s, ⟨hp.1.2.1, hs⟩, rfl, rfl, rfl, rfl⟩, hp⟩

def CompleteQuintic (f : Quintic) (L : List AffineCode) : Prop :=
  ∀ p, p ∈ L ↔ AffinePoint f p

theorem boundedPoints_complete_iff (f : Quintic) (B : Nat) :
    CompleteQuintic f (boundedPoints f B) ↔ HeightBound f B := by
  constructor
  · intro h p hp
    exact ((boundedPoints_spec f B p).mp ((h p).mpr hp)).2
  · intro h p
    constructor
    · intro hm
      exact ((boundedPoints_spec f B p).mp hm).1
    · intro hp
      exact (boundedPoints_spec f B p).mpr ⟨hp, h p hp⟩

def listHeight : List AffineCode → Nat
  | [] => 0
  | p :: ps => max (height p) (listHeight ps)

theorem height_le_listHeight {L : List AffineCode} {p : AffineCode}
    (h : p ∈ L) : height p ≤ listHeight L := by
  induction L with
  | nil => simp at h
  | cons q qs ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · subst p
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem positiveQuintic_iff_height (f : Quintic) :
    (∃ L, CompleteQuintic f L) ↔ ∃ B, HeightBound f B := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨listHeight L, fun p hp => height_le_listHeight ((hL p).mpr hp)⟩
  · rintro ⟨B, hB⟩
    exact ⟨boundedPoints f B, (boundedPoints_complete_iff f B).mpr hB⟩

/-- A family with a direct sign obstruction: y²=-(x^(2g+2)+1).
The inputs a,c stand for absolute numerator values. -/
def NegativeEvenAffineEquation (g a b c d : Nat) : Prop :=
  c*c*b^(2*g+2) + d*d*a^(2*g+2) + d*d*b^(2*g+2) = 0

theorem negativeEven_no_affine (g a b c d : Nat)
    (hb : 0 < b) (hd : 0 < d) :
    ¬ NegativeEvenAffineEquation g a b c d := by
  intro h
  have hpow : 0 < b^(2*g+2) := Nat.pow_pos hb
  have hlast : 0 < d*d*b^(2*g+2) :=
    Nat.mul_pos (Nat.mul_pos hd hd) hpow
  unfold NegativeEvenAffineEquation at h
  exact (Nat.ne_of_gt hlast) (Nat.add_eq_zero_iff.mp h).2

theorem negativeEven_no_infinity (c d : Nat) (hd : 0 < d) :
    c*c + d*d ≠ 0 := by
  have hpos := Nat.mul_pos hd hd
  intro h
  exact (Nat.ne_of_gt hpos) (Nat.add_eq_zero_iff.mp h).2

example : AffinePoint ⟨1,-1,0,0,0⟩ ⟨0,1,1,1⟩ := by decide
example : AffinePoint ⟨1,-1,0,0,0⟩ ⟨1,1,-1,1⟩ := by decide
example : height ⟨-2,3,5,7⟩ = 7 := by decide

end FaltingsAudit

#print axioms FaltingsAudit.uniformData_implies_goal
#print axioms FaltingsAudit.boundedPoints_spec
#print axioms FaltingsAudit.positiveQuintic_iff_height
#print axioms FaltingsAudit.negativeEven_no_affine
#print axioms FaltingsAudit.negativeEven_no_infinity
