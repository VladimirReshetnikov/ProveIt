import GRHArticle.ClassGroups.ReducedQuadraticForms
import GRHArticle.SingularModuli.ReducedForms

/-!
# Agreement with the existing singular-moduli reduced forms

The list computation keeps the positive outer coefficients as naturals.
After restoring the types of the singular-moduli coefficients, its
duplicate-free enumeration is the same collection of reduced forms.
-/

namespace GRHArticle.ClassGroups

open GRHArticle.SingularModuli

private theorem int_abs_eq_cast_natAbs (b : ℤ) : |b| = (b.natAbs : ℤ) := by
  by_cases h : 0 ≤ b
  · rw [abs_of_nonneg h, Int.natAbs_of_nonneg h]
  · have hn : b ≤ 0 := by omega
    rw [abs_of_nonpos hn, Int.ofNat_natAbs_of_nonpos hn]

private theorem int_square_cast_natAbs (b : ℤ) : (b.natAbs : ℤ)^2 = b^2 := by
  by_cases h : 0 ≤ b
  · rw [Int.natAbs_of_nonneg h]
  · rw [Int.ofNat_natAbs_of_nonpos (by omega : b ≤ 0), neg_sq]

private def toSingularForm (f : ReducedQuadraticForm) (ha : 0 < f.a) : FormCoefficients :=
  ⟨⟨f.a,ha⟩,f.b,f.c⟩

private theorem primitiveReducedAt_iff_singular (D : ℕ+) (f : ReducedQuadraticForm) (ha : 0 < f.a) :
    PrimitiveReducedAt D f ↔ IsPrimitiveReducedForm D (toSingularForm f ha) := by
  have hdisc : f.b.natAbs^2+(D:ℕ) = 4*f.a*f.c ↔
      f.b^2-4*(f.a:ℤ)*f.c = -(D:ℤ) := by
    rw [← Int.ofNat_inj]
    push_cast
    rw [int_abs_eq_cast_natAbs, int_square_cast_natAbs]
    omega
  have hbound (hb : f.b.natAbs ≤ f.a) (hc : f.a ≤ f.c) :
      (0 ≤ f.b ∨ (f.b.natAbs < f.a ∧ f.a < f.c)) ↔
        ((f.b.natAbs = f.a ∨ f.a = f.c) → 0 ≤ f.b) := by
    omega
  constructor
  · rintro ⟨_,hb,hc,hd,hg,hm⟩
    have he := (hbound hb hc).mp hm
    refine ⟨hdisc.mp hd, ?_, Int.ofNat_le.mpr hc, ?_, ?_⟩
    · change |f.b| ≤ (f.a:ℤ)
      rw [int_abs_eq_cast_natAbs]
      exact Int.ofNat_le.mpr hb
    · change (|f.b| = (f.a:ℤ) ∨ (f.a:ℤ) = f.c) → 0 ≤ f.b
      simpa only [int_abs_eq_cast_natAbs, Int.ofNat_inj] using he
    · change Nat.gcd (Nat.gcd f.a f.b.natAbs) (f.c:ℤ).natAbs = 1
      simpa only [Int.natAbs_natCast, Nat.gcd_assoc] using hg
  · rintro ⟨hd,hb,hc,hm,hg⟩
    change |f.b| ≤ (f.a:ℤ) at hb
    rw [int_abs_eq_cast_natAbs, Int.ofNat_le] at hb
    have hc' : f.a ≤ f.c := Int.ofNat_le.mp hc
    refine ⟨ha,hb,hc',hdisc.mpr hd,?_,(hbound hb hc').mpr ?_⟩
    · change Nat.gcd (Nat.gcd f.a f.b.natAbs) (f.c:ℤ).natAbs = 1 at hg
      simpa only [Int.natAbs_natCast, Nat.gcd_assoc] using hg
    · change (|f.b| = (f.a:ℤ) ∨ (f.a:ℤ) = f.c) → 0 ≤ f.b at hm
      simpa only [int_abs_eq_cast_natAbs, Int.ofNat_inj] using hm

/-- The efficient list count equals the existing singular-moduli finset cardinality. -/
theorem reducedQuadraticFormCount_eq_reducedForms_card (D : ℕ+) :
    reducedQuadraticFormCount D = (reducedForms D).card := by
  let A := (reducedQuadraticForms D).toFinset
  have hA : reducedQuadraticFormCount D = A.card :=
    (List.toFinset_card_of_nodup (nodup_reducedQuadraticForms D)).symm
  rw [hA]
  have valid (f : ReducedQuadraticForm) (hf : f ∈ A) : PrimitiveReducedAt D f :=
    mem_reducedQuadraticForms.mp (List.mem_toFinset.mp hf)
  apply Finset.card_bij (fun f hf ↦ toSingularForm f (valid f hf).1)
  · exact fun f hf ↦ (mem_reducedForms_iff D _).mpr
      ((primitiveReducedAt_iff_singular D f _).mp (valid f hf))
  · intro f _ g _ he
    ext
    · exact congrArg (fun z : FormCoefficients ↦ (z.a : ℕ)) he
    · exact congrArg FormCoefficients.b he
    · exact Int.ofNat_inj.mp (congrArg FormCoefficients.c he)
  · intro f hf
    have hvalid := (mem_reducedForms_iff D f).mp hf
    rcases f with ⟨a,b,c⟩
    let g : ReducedQuadraticForm := ⟨a,b,c.toNat⟩
    have ha : 0 < g.a := a.pos
    have hc : 0 ≤ c := by
      have h := hvalid.2.2.1
      change (a:ℤ) ≤ c at h
      omega
    have hsame (h : 0 < g.a) : toSingularForm g h = ⟨a,b,c⟩ := by
      simp only [toSingularForm,g,Int.toNat_of_nonneg hc]
      congr 1
    have hg : PrimitiveReducedAt D g := (primitiveReducedAt_iff_singular D g ha).mpr
      (hsame ha ▸ hvalid)
    exact ⟨g, List.mem_toFinset.mpr (mem_reducedQuadraticForms.mpr hg), hsame _⟩

end GRHArticle.ClassGroups
