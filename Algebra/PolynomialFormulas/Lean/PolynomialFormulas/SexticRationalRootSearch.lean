import PolynomialFormulas.SexticSeparatingSearch

/-!
# Recursive rational-root search for computed monic resolvents

Ascending integer coefficient lists are evaluated by Horner recursion.  For a
monic list polynomial, every rational root is an integer, and every nonzero
integer root divides the constant coefficient.  Thus a finite zig-zag search
through that divisibility bound is complete.
-/

open Polynomial
open Denumerable Encodable Function

namespace LeanProofs.PolynomialFormulas.SexticRationalRootSearch

open QuinticRadicalDecidability
open QuinticRadicalPrimrec

def evalInt (cs : List ℤ) (z : ℤ) : ℤ :=
  cs.foldr (fun a s ↦ a + z * s) 0

noncomputable def toPolynomial : List ℤ → ℤ[X]
  | [] => 0
  | a :: cs => Polynomial.C a + Polynomial.X * toPolynomial cs

@[simp] theorem toPolynomial_nil : toPolynomial [] = 0 := rfl

@[simp] theorem toPolynomial_cons (a : ℤ) (cs : List ℤ) :
    toPolynomial (a :: cs) =
      Polynomial.C a + Polynomial.X * toPolynomial cs := rfl

@[simp] theorem coeff_toPolynomial (cs : List ℤ) (n : ℕ) :
    (toPolynomial cs).coeff n = cs.getD n 0 := by
  induction cs generalizing n with
  | nil => simp
  | cons a cs ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [toPolynomial_cons, Polynomial.coeff_add,
            Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero n),
            zero_add, Polynomial.coeff_X_mul, ih]
          rfl

theorem aeval_toPolynomial_int (cs : List ℤ) (z : ℤ) :
    aeval z (toPolynomial cs) = evalInt cs z := by
  induction cs with
  | nil => simp [evalInt]
  | cons a cs ih =>
      rw [toPolynomial_cons, map_add, aeval_C, map_mul, aeval_X, ih]
      rfl

theorem aeval_toPolynomial_rat_int (cs : List ℤ) (z : ℤ) :
    aeval (z : ℚ) (toPolynomial cs) = (evalInt cs z : ℚ) := by
  induction cs with
  | nil => simp [evalInt]
  | cons a cs ih =>
      rw [toPolynomial_cons, map_add, aeval_C, map_mul, aeval_X, ih]
      simp only [evalInt, List.foldr_cons]
      simpa only [algebraMap_int_eq, Int.coe_castRingHom,
        Int.cast_add, Int.cast_mul]

theorem evalInt_primrec : Primrec₂ evalInt := by
  change Primrec fun u : List ℤ × ℤ ↦ evalInt u.1 u.2
  have hstep : Primrec₂ fun u : List ℤ × ℤ ↦
      fun v : ℤ × ℤ ↦ v.1 + u.2 * v.2 := by
    change Primrec fun u : (List ℤ × ℤ) × (ℤ × ℤ) ↦
      u.2.1 + u.1.2 * u.2.2
    exact int_add_primrec.comp (Primrec.fst.comp Primrec.snd)
      (int_mul_primrec.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.fst (Primrec.const 0) hstep).of_eq
    fun u ↦ by rfl

def constantCoeff (cs : List ℤ) : ℤ := cs.getD 0 0

theorem constantCoeff_primrec : Primrec constantCoeff :=
  (Primrec.list_getD (0 : ℤ)).comp Primrec.id (Primrec.const 0)

def HasCodedIntegerRoot (cs : List ℤ) : Prop :=
  constantCoeff cs = 0 ∨
    ∃ n < symmetricCodeBound (constantCoeff cs).natAbs,
      evalInt cs (ofNat ℤ n) = 0

instance (cs : List ℤ) : Decidable (HasCodedIntegerRoot cs) :=
  inferInstanceAs (Decidable
    (constantCoeff cs = 0 ∨
      ∃ n < symmetricCodeBound (constantCoeff cs).natAbs,
        evalInt cs (ofNat ℤ n) = 0))

def rationalRootSearch (cs : List ℤ) : Bool :=
  decide (HasCodedIntegerRoot cs)

def HasRationalRoot (cs : List ℤ) : Prop :=
  ∃ q : ℚ, aeval q (toPolynomial cs) = 0

theorem hasCodedIntegerRoot_primrec : PrimrecPred HasCodedIntegerRoot := by
  have htest : PrimrecRel fun n : ℕ ↦ fun cs : List ℤ ↦
      evalInt cs (ofNat ℤ n) = 0 := by
    change PrimrecPred fun u : ℕ × List ℤ ↦
      evalInt u.2 (ofNat ℤ u.1) = 0
    exact Primrec.eq.comp
      (evalInt_primrec.comp Primrec.snd
        ((Primrec.ofNat ℤ).comp Primrec.fst))
      (Primrec.const 0)
  have hbound : Primrec fun cs : List ℤ ↦
      symmetricCodeBound (constantCoeff cs).natAbs :=
    symmetricCodeBound_primrec.comp
      (int_natAbs_primrec.comp constantCoeff_primrec)
  have hexists : PrimrecPred fun cs : List ℤ ↦
      ∃ n < symmetricCodeBound (constantCoeff cs).natAbs,
        evalInt cs (ofNat ℤ n) = 0 :=
    primrecPred_exists_lt htest hbound
  have hzero : PrimrecPred fun cs : List ℤ ↦ constantCoeff cs = 0 :=
    Primrec.eq.comp constantCoeff_primrec (Primrec.const 0)
  exact hzero.or hexists

theorem rationalRootSearch_primrec : Primrec rationalRootSearch :=
  hasCodedIntegerRoot_primrec.decide

theorem hasRationalRoot_of_hasCodedIntegerRoot (cs : List ℤ)
    (h : HasCodedIntegerRoot cs) : HasRationalRoot cs := by
  rcases h with hzero | ⟨n, hn, heval⟩
  · refine ⟨0, ?_⟩
    cases cs with
    | nil => simp [toPolynomial]
    | cons a cs => simpa [constantCoeff] using hzero
  · refine ⟨(ofNat ℤ n : ℚ), ?_⟩
    rw [aeval_toPolynomial_rat_int, heval]
    norm_num

theorem integer_dvd_constantCoeff_of_evalInt_eq_zero
    (cs : List ℤ) (z : ℤ) (hz : evalInt cs z = 0) :
    z ∣ constantCoeff cs := by
  cases cs with
  | nil => simp [constantCoeff]
  | cons a cs =>
      refine ⟨-evalInt cs z, ?_⟩
      simp only [evalInt, List.foldr_cons] at hz
      change a = z * -evalInt cs z
      calc
        a = -(z * evalInt cs z) := eq_neg_of_add_eq_zero_left hz
        _ = z * -evalInt cs z := by ring

theorem hasCodedIntegerRoot_of_hasRationalRoot (cs : List ℤ)
    (hmonic : (toPolynomial cs).Monic)
    (h : HasRationalRoot cs) : HasCodedIntegerRoot cs := by
  rcases h with ⟨q, hq⟩
  by_cases hzero : constantCoeff cs = 0
  · exact Or.inl hzero
  · right
    have hIntegral : IsIntegral ℤ q := ⟨toPolynomial cs, hmonic, hq⟩
    obtain ⟨z : ℤ, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hIntegral
    have hqz : q = (z : ℚ) := hz.symm
    have hevalCast : (evalInt cs z : ℚ) = 0 := by
      rw [← aeval_toPolynomial_rat_int, ← hqz, hq]
    have heval : evalInt cs z = 0 := by exact_mod_cast hevalCast
    have hdvd := integer_dvd_constantCoeff_of_evalInt_eq_zero cs z heval
    have habs : z.natAbs ≤ (constantCoeff cs).natAbs :=
      Int.natAbs_le_of_dvd_ne_zero hdvd hzero
    refine ⟨Equiv.intEquivNat z, ?_, ?_⟩
    · exact (intEquivNat_lt_iff_mem_symmetricInterval z
        (constantCoeff cs).natAbs).mpr <| by
        rw [mem_symmetricInterval]
        have habsZ : (z.natAbs : ℤ) ≤
            ((constantCoeff cs).natAbs : ℤ) := by exact_mod_cast habs
        rw [Int.natCast_natAbs] at habsZ
        constructor <;> omega
    · change evalInt cs (Equiv.intEquivNat.symm (Equiv.intEquivNat z)) = 0
      simpa using heval

theorem rationalRootSearch_iff (cs : List ℤ)
    (hmonic : (toPolynomial cs).Monic) :
    rationalRootSearch cs = true ↔ HasRationalRoot cs := by
  rw [rationalRootSearch, decide_eq_true_eq]
  exact ⟨hasRationalRoot_of_hasCodedIntegerRoot cs,
    hasCodedIntegerRoot_of_hasRationalRoot cs hmonic⟩

end LeanProofs.PolynomialFormulas.SexticRationalRootSearch
