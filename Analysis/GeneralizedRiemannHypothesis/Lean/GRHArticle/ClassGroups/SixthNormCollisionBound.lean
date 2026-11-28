import GRHArticle.ClassGroups.SixthNormPairReduction

/-!
# The sixth-power norm pigeonhole obstruction

Inertness at the witness primes and the norm equations are kept explicit.
The finite pair certificates give injectivity of the positive coefficients,
and the norm bound puts all of them in a set of size eighteen.
-/

namespace GRHArticle.ClassGroups

/-- The small witness primes cannot admit a nonzero square root of `-x`. -/
def NoSixthDiscriminantSquareWitness (x : ℕ) : Prop :=
  ∀ r, r.Prime → 19 ≤ r → r ≤ 151 → ∀ a : ZMod r, a ≠ 0 → a^2 ≠ -(x:ZMod r)

/-- The large-discriminant regime permits at most eighteen split-prime norm
equations when all pairs in the stated finite range have been checked. -/
theorem sixthPowerNormSet_card_le_of_verified_pairs {Y x : ℕ} (hY : Y ≤ 5500)
    (hx : censusDiscriminantCutoff < x) (hno : NoSixthDiscriminantSquareWitness x)
    (hchecked : ∀ {p q : ℕ}, p.Prime → q.Prime → p < q → q ≤ Y →
      censusDiscriminantCutoff < 4*p^6 → checkSixthNormPair p q = true)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Y)
    (hnorm : ∀ p ∈ S, ∃ a b : ℕ, 0 < b ∧ SixthPowerNormEquation x p a b) :
    S.card ≤ 18 := by
  classical
  have hN (p : ↥S) : ∃ a b : ℕ, 0 < b ∧ SixthPowerNormEquation x p.val a b :=
    hnorm p.val p.property
  choose a b hb he using hN
  have hbound (p : ↥S) : b p ≤ 18 :=
    sixthPowerNorm_coefficient_le hx ((hS p.val p.property).2.trans hY) (he p)
  have hcut (p : ↥S) : censusDiscriminantCutoff < x*(b p)^2 :=
    hx.trans_le (Nat.le_mul_of_pos_right _ (pow_pos (hb p) _))
  have hlt (p q : ↥S) (hpq : p.val < q.val) (hs : b p = b q) : False := by
    have hp : p.val.Prime := (hS p.val p.property).1
    obtain ⟨hq,hqY⟩ := hS q.val q.property
    have hc : censusDiscriminantCutoff < 4*p.val^6 := by
      have hn : (a p)^2+x*(b p)^2 = 4*p.val^6 := he p
      have hc := hcut p
      omega
    have hqnorm : SixthPowerNormEquation x q.val (a q) (b p) := hs ▸ he q
    obtain ⟨u,hd,hl,hu,hm⟩ := exists_sixthNormCandidate_of_collision
      (by omega) hpq (hb p) (he p) hqnorm
    have hM : censusDiscriminantCutoff < sixthNormCandidate p.val q.val u := hm ▸ hcut p
    have hW := hasSixthSquareWitness_of_pairCheck hpq hd hl hu hM (hchecked hp hq hpq hqY hc)
    rw [hm] at hW
    obtain ⟨r,hr,hlo,hhi,j,hj,hjs⟩ := discriminantSquareWitness_of_sixthWitness hW
    exact hno r hr hlo hhi j hj hjs
  let f (p : ↥S) : Fin 18 := ⟨b p-1, by have := hb p; have := hbound p; omega⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have heq : b p = b q := by
      have ht := congrArg Fin.val hpq
      change b p-1 = b q-1 at ht
      have hpos := hb p
      have hpos' := hb q
      omega
    rcases lt_trichotomy p.val q.val with h | h | h
    · exact (hlt p q h heq).elim
    · exact Subtype.ext h
    · exact (hlt q p h heq.symm).elim
  simpa using Fintype.card_le_of_injective f hf

end GRHArticle.ClassGroups
