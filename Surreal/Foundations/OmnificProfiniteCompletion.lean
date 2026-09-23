import Surreal.Algebra.IntegerCongruenceLimit
import Surreal.Foundations.OmnificFiniteQuotients

/-!
# The profinite completion of the actual omnific ring

The profinite ring-isomorphism clause of `odg:eq:profinite`, with its
canonical map and kernel. The source specifies the set-sized inverse limit
over positive ordinary moduli, ordered by divisibility. We use that exact
diagram, whose limit universal property is proved in `IntegerCongruenceLimit`.
The target is the ordinary inverse limit of the integer quotient rings.
-/

universe u

namespace Surreal.Foundations.SignSequence

open IntegerCongruenceLimit

noncomputable section

/-- The actual omnific congruence quotient equals the ordinary integer quotient. -/
def omnificCongruenceQuotientEquiv (n : Modulus) :
    OmnificInteger.{u} ⧸ ideal OmnificInteger n ≃+* ℤ ⧸ ideal ℤ n :=
  (Ideal.quotEquivOfEq (show ideal OmnificInteger n =
    Ideal.span {omnificIntCast (n.val : ℤ)} by
      rw [ideal, map_natCast])).trans
    (omnificQuotientIntEquiv (n.val : ℤ) (by exact_mod_cast n.positive.ne'))

/-- Each component isomorphism takes the ordinary residue of the integer constant term. -/
@[simp] theorem omnificCongruenceQuotientEquiv_mk (n : Modulus) (x : OmnificInteger.{u}) :
    omnificCongruenceQuotientEquiv n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk (ideal ℤ n) (omnificConstantCoeff x) := rfl

/-- The quotient isomorphisms respect every divisibility reduction, not just prime powers. -/
theorem omnificCongruenceQuotientEquiv_compatible {m n : Modulus} (h : m ≤ n)
    (x : OmnificInteger.{u} ⧸ ideal OmnificInteger m) :
    omnificCongruenceQuotientEquiv n (Ideal.Quotient.factor (ideal_le OmnificInteger h) x) =
      Ideal.Quotient.factor (ideal_le ℤ h) (omnificCongruenceQuotientEquiv m x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk, omnificCongruenceQuotientEquiv_mk]

/-- Every quotient in the ordinary-modulus diagram is finite. -/
theorem omnificCongruenceQuotient_finite (n : Modulus) :
    Finite (OmnificInteger.{u} ⧸ ideal OmnificInteger n) := by
  letI : NeZero n.val := ⟨n.positive.ne'⟩
  let e := (omnificCongruenceQuotientEquiv.{u} n).trans (Int.quotientSpanNatEquivZMod n.val)
  exact Finite.of_injective e e.injective

/-- Every finite-index omnific ideal occurs in the positive-modulus diagram, including the unit ideal. -/
theorem omnific_finite_ideal_in_congruence_diagram (I : Ideal OmnificInteger.{u})
    [Finite (OmnificInteger.{u} ⧸ I)] : ∃ n : Modulus, I = ideal OmnificInteger n := by
  by_cases htop : I = ⊤
  · refine ⟨⟨1, Nat.zero_lt_one⟩, ?_⟩
    simpa only [ideal, Nat.cast_one, Ideal.span_singleton_one] using htop
  have hm : (ringChar (OmnificInteger.{u} ⧸ I) : ℤ) ≠ 0 := by
    exact_mod_cast CharP.ringChar_ne_zero_of_finite (OmnificInteger.{u} ⧸ I)
  have hmem : omnificIntCast (ringChar (OmnificInteger.{u} ⧸ I) : ℤ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, omnific_hom_intCast, Int.cast_natCast,
      CharP.cast_eq_zero (OmnificInteger.{u} ⧸ I) (ringChar (OmnificInteger.{u} ⧸ I))]
  obtain ⟨n, ⟨hn, hI⟩, _⟩ := omnific_ideal_existsUnique_modulus I htop ⟨_, hm, hmem⟩
  refine ⟨⟨n, by omega⟩, ?_⟩
  simpa only [ideal, map_natCast] using hI

/-- The omnific profinite completion, as the specified positive-modulus inverse limit. -/
abbrev OmnificProfiniteCompletion := IntegerCongruenceLimit.Completion OmnificInteger.{u}

/-- The ordinary profinite integer ring as the inverse limit of `ℤ/nℤ` for positive `n`. -/
abbrev ProfiniteInteger := IntegerCongruenceLimit.Completion ℤ

/-- Constant-term residues induce the profinite ring isomorphism. -/
def omnificProfiniteCompletionEquiv : OmnificProfiniteCompletion.{u} ≃+* ProfiniteInteger :=
  IntegerCongruenceLimit.congr omnificCongruenceQuotientEquiv
    omnificCongruenceQuotientEquiv_compatible

/-- The profinite isomorphism preserves the constant-term quotient map at every modulus. -/
@[simp] theorem projection_omnificProfiniteCompletionEquiv (n : Modulus)
    (x : OmnificProfiniteCompletion.{u}) :
    projection ℤ n (omnificProfiniteCompletionEquiv x) =
      omnificCongruenceQuotientEquiv n (projection OmnificInteger n x) := rfl

/-- The canonical omnific map to its profinite completion. -/
def omnificProfiniteMap : OmnificInteger.{u} →+* OmnificProfiniteCompletion :=
  IntegerCongruenceLimit.of OmnificInteger

/-- The completion map is constant extraction followed by the canonical integer completion map. -/
theorem omnificProfiniteCompletionEquiv_of (x : OmnificInteger.{u}) :
    omnificProfiniteCompletionEquiv (omnificProfiniteMap x) =
      IntegerCongruenceLimit.of ℤ (omnificConstantCoeff x) := by
  apply IntegerCongruenceLimit.ext ℤ
  intro n
  rw [projection_omnificProfiniteCompletionEquiv]
  change omnificCongruenceQuotientEquiv n (projection OmnificInteger n
    (IntegerCongruenceLimit.of OmnificInteger x)) = _
  rw [projection_of, omnificCongruenceQuotientEquiv_mk, projection_of]

/-- The profinite completion kills precisely the purely infinite ideal. -/
theorem omnificProfiniteMap_eq_zero_iff (x : OmnificInteger.{u}) :
    omnificProfiniteMap x = 0 ↔ x ∈ omnificPurelyInfiniteIdeal := by
  rw [omnificProfiniteMap, IntegerCongruenceLimit.of_eq_zero_iff,
    ← omnific_dvd_all_pos_int_iff]
  simp only [Ideal.mem_iInf, ideal, Ideal.mem_span_singleton, map_natCast]
  constructor
  · intro h n hn
    exact h ⟨n, hn⟩
  · intro h n
    exact h n.val n.positive

/-- The profinite completion map has exactly the purely infinite kernel as an ideal. -/
theorem ker_omnificProfiniteMap :
    RingHom.ker omnificProfiniteMap = omnificPurelyInfiniteIdeal.{u} := by
  ext x
  exact omnificProfiniteMap_eq_zero_iff x

end
end Surreal.Foundations.SignSequence
