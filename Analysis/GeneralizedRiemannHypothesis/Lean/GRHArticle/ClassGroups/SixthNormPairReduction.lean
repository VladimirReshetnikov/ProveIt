import GRHArticle.ClassGroups.SixthNormPairSearch
import Mathlib.Data.ZMod.Basic

/-!
# From equal coefficients to a sixth-power norm candidate

Subtracting the two norm equations yields a product of the half-sum
and half-difference. The small-prime square witness for the candidate
also supplies a nonzero square witness for the discriminant.
-/

namespace GRHArticle.ClassGroups

/-- The equation obtained from a principal sixth power of a split prime ideal. -/
def SixthPowerNormEquation (x p a b : ℕ) : Prop :=
  a^2+x*b^2 = 4*p^6

private theorem sq_mod_two (n : ℕ) : n^2%2 = n%2 := by
  rw [Nat.pow_mod]
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h | h <;> simp [h]

private theorem sixthPowerDifference_cubeFactor {p q : ℕ} (h : p < q) :
    q^6-p^6 = (q^3-p^3)*(q^3+p^3) := by
  have hp₃ : p^3 ≤ q^3 := Nat.pow_le_pow_left h.le _
  have hp₆ : p^6 ≤ q^6 := Nat.pow_le_pow_left h.le _
  zify [hp₃,hp₆]
  ring

/-- Equal positive norm coefficients give a candidate in precisely the
divisor interval used by the finite check. -/
theorem exists_sixthNormCandidate_of_collision {x p q a c b : ℕ}
    (hx : 0 < x) (hpq : p < q) (hb : 0 < b)
    (ha : SixthPowerNormEquation x p a b) (hc : SixthPowerNormEquation x q c b) :
    ∃ u, u ∣ q^6-p^6 ∧ q^3-p^3 < u ∧ u ≤ (q^6-p^6).sqrt ∧
      sixthNormCandidate p q u = x*b^2 := by
  unfold SixthPowerNormEquation at ha hc
  have hxb : 0 < x*b^2 := mul_pos hx (pow_pos hb _)
  have hp₆ : p^6 < q^6 := Nat.pow_lt_pow_left hpq (by decide)
  have hp₃ : p^3 < q^3 := Nat.pow_lt_pow_left hpq (by decide)
  have hsq : a^2 < c^2 := by omega
  have hac : a < c := by
    by_contra! h
    exact hsq.not_ge (Nat.pow_le_pow_left h _)
  let N := q^6-p^6
  have hdiff : c^2 = a^2+4*N := by dsimp [N]; omega
  have hpar := congrArg (· % (2:ℕ)) hdiff
  have hmod : (a^2+4*N)%2 = a^2%2 := by omega
  rw [hmod, sq_mod_two, sq_mod_two] at hpar
  let u := (c-a)/2
  let v := (c+a)/2
  have hu : 2*u = c-a := by dsimp [u]; omega
  have hv : 2*v = c+a := by dsimp [v]; omega
  have hu₀ : 0 < u := by omega
  have huv : u ≤ v := by omega
  have hva : v-u = a := by omega
  have hmul : u*v = N := by
    have hprod : 4*(u*v) = c^2-a^2 := by
      calc
        _ = (2*u)*(2*v) := by ring
        _ = (c-a)*(c+a) := by rw [hu,hv]
        _ = _ := by
          zify [hac.le,hsq.le]
          ring
    omega
  have hdiv : N/u = v := by rw [← hmul, Nat.mul_div_cancel_left _ hu₀]
  have hleft : q^3-p^3 < u := by
    by_contra! h
    have hfactor : N = (q^3-p^3)*(q^3+p^3) := sixthPowerDifference_cubeFactor hpq
    have hcomp : u*(q^3+p^3) ≤ u*v :=
      (Nat.mul_le_mul_right _ h).trans_eq (hfactor.symm.trans hmul.symm)
    have hlow : q^3+p^3 ≤ v := Nat.le_of_mul_le_mul_left hcomp hu₀
    have hlow' : 2*p^3 ≤ a := by omega
    have hbound := Nat.pow_le_pow_left hlow' 2
    have hpow : (2*p^3)^2 = 4*p^6 := by ring
    rw [hpow] at hbound
    omega
  have hright : u ≤ N.sqrt := Nat.le_sqrt.mpr
    ((Nat.mul_le_mul_left u huv).trans_eq hmul)
  refine ⟨u, ⟨v,hmul.symm⟩, hleft, hright, ?_⟩
  change 4*p^6 - (N/u-u)^2 = x*b^2
  rw [hdiv,hva]
  omega

/-- The admissible coefficient range for exponent six in the article. -/
theorem sixthPowerNorm_coefficient_le {x p a b : ℕ} (hx : censusDiscriminantCutoff < x)
    (hp : p ≤ 5500) (h : SixthPowerNormEquation x p a b) : b ≤ 18 := by
  by_contra! hb
  have hnum : 4*5500^6 < 19^2*censusDiscriminantCutoff := by decide +kernel
  have hp' := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hp 6)
  have hb' : 19^2*censusDiscriminantCutoff ≤ b^2*x :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : 19 ≤ b) 2) hx.le
  rw [mul_comm (b^2) x] at hb'
  unfold SixthPowerNormEquation at h
  omega

/-- The article's elementary exclusion of split primes at most 2000. -/
theorem sixthPowerNorm_prime_large {x p a b : ℕ} (hx : censusDiscriminantCutoff < x)
    (hb : 0 < b) (h : SixthPowerNormEquation x p a b) : 2000 < p := by
  by_contra! hp
  have hnum : 4*2000^6 < censusDiscriminantCutoff := by decide +kernel
  have hp' := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hp 6)
  have hb' : x ≤ x*b^2 := Nat.le_mul_of_pos_right _ (pow_pos hb _)
  unfold SixthPowerNormEquation at h
  omega

/-- A modular witness for `-xb²` excludes a discriminant whose negative
is required to be a nonsquare at all witness primes. -/
theorem discriminantSquareWitness_of_sixthWitness {x b : ℕ}
    (h : HasSixthSquareWitness (x*b^2)) :
    ∃ r, r.Prime ∧ 19 ≤ r ∧ r ≤ 151 ∧
      ∃ a : ZMod r, a ≠ 0 ∧ a^2 = -(x:ZMod r) := by
  obtain ⟨r,hr,hlo,hhi,hM,j,hj₀,hjr,hj⟩ := h
  letI : Fact r.Prime := ⟨hr⟩
  let M := x*b^2
  have hM' : (M : ZMod r) ≠ 0 := by
    intro hz
    have he := congrArg ZMod.val hz
    exact hM (by simpa only [M, ZMod.val_natCast, ZMod.val_zero] using he)
  have hb' : (b : ZMod r) ≠ 0 := by
    intro hb₀
    apply hM'
    simp [M, hb₀]
  have hj' : (j : ZMod r) ≠ 0 := by
    intro hz
    have he := congrArg ZMod.val hz
    exact hj₀.ne' (by simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hjr] using he)
  have hs : (j:ZMod r)^2 = -(M:ZMod r) := by
    have h := congrArg (fun n : ℕ ↦ (n : ZMod r)) hj
    simpa [Nat.cast_sub (Nat.mod_lt M hr.pos).le, M] using h
  refine ⟨r,hr,hlo,hhi,(j:ZMod r)/(b:ZMod r),div_ne_zero hj' hb',?_⟩
  rw [div_pow, hs]
  simp only [M, Nat.cast_mul, Nat.cast_pow, ← neg_mul]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ hb')

end GRHArticle.ClassGroups
