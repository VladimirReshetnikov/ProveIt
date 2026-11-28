import GRHArticle.SingularModuli.HeckeSeriesPrefixArithmetic
import GRHArticle.SingularModuli.HeckeIntegerTraceRecursion
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Finite integer computations for prime diagonal certificates

The coefficient lists use increasing index order. All intermediate
products are truncated to the length needed by the certificate.
-/

namespace GRHArticle.SingularModuli

open SeriesPrefix

/-- The normalized modular invariant coefficients through index `N-1`. -/
def normalizedJCoefficientPrefix (N : ℕ) : List ℤ :=
  let σ := ArithmeticFunction.sigma
  let a := read (N+1) fun n ↦ (σ 3 n : ℤ)
  let b := read (N+1) fun n ↦ (σ 5 n : ℤ)
  let linear := read (N+1) fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)
  let discr :=
    sub (N+1)
      (add (N+1) (add (N+1) linear (scale (N+1) 100 (pow (N+1) a 2)))
        (scale (N+1) 8000 (pow (N+1) a 3)))
      (scale (N+1) 147 (pow (N+1) b 2))
  let discrUnit := read N fun n ↦ discr.getD (n+1) 0
  let e4 := add N (read N fun n ↦ if n = 0 then 1 else 0) (scale N 240 a)
  multiplyPackedIntegerPolynomial N (pow N e4 3) (inverseUnit N discrUnit (N.log2+1))

private def prefixPowerTable (N : ℕ) (xs : List ℤ) : ℕ → Array (List ℤ)
  | 0 => #[read N fun n ↦ if n = 0 then 1 else 0]
  | k+1 =>
    let tab := prefixPowerTable N xs k
    tab.push (multiplyPackedIntegerPolynomial N tab[k]! xs)

private def tracePowerPrefix (p k N : ℕ) (s : Array (List ℤ)) : List ℤ :=
  read N fun n ↦ if (p - 1)*k ≤ p*n then (p : ℤ) * (s[k]!).getD (p*n-(p-1)*k) 0 else 0

private def sumPrefixes (N : ℕ) : List (List ℤ) → List ℤ
  | [] => read N fun _ ↦ 0
  | xs :: rest => add N xs (sumPrefixes N rest)

private def scaledElementaryTable (p N : ℕ) (powers : Array (List ℤ)) : ℕ → Array (List ℤ)
  | 0 => #[read N fun n ↦ if n = 0 then 1 else 0]
  | k+1 =>
    let tab := scaledElementaryTable p N powers k
    let next := sumPrefixes N <| List.ofFn fun i : Fin (k+1) ↦
      scale N ((-1 : ℤ) ^ (k+2+(i : ℕ)) * ↑(k.factorial / (i : ℕ).factorial))
        (multiplyPackedIntegerPolynomial N tab[(i : ℕ)]! (tracePowerPrefix p (k+1-i) N powers))
    tab.push next

/-- The signed prime diagonal normalized at the cusp and scaled by `p!`,
truncated to the coefficient range needed for the degree bound. -/
def computedScaledDiagonalPrefix (p : ℕ) : List ℤ :=
  let N := 2*p+1
  let M := 2*p*p+1
  let jAll := normalizedJCoefficientPrefix M
  let jSmall := jAll.take N
  let powers := prefixPowerTable M jAll p
  let elementary := scaledElementaryTable p N powers p
  let smallPowers := prefixPowerTable N jSmall p
  let factors := sumPrefixes N <| List.ofFn fun k : Fin (p+1) ↦
    scale N ((-1 : ℤ) ^ (k : ℕ) * ↑(p.factorial / (k : ℕ).factorial))
      (multiplyPackedIntegerPolynomial N elementary[(k : ℕ)]! smallPowers[p-k]!)
  let front := sub N (substitutePower N p jSmall) (shift N (p-1) jSmall)
  multiplyPackedIntegerPolynomial N front factors

private def clearedPrefix (N : ℕ) (coeffs : List ℤ) (powers : Array (List ℤ)) :
    ℕ → List ℤ
  | 0 => read N fun n ↦ if n = 0 then coeffs.getD 0 0 else 0
  | k+1 => add N (shift N 1 (clearedPrefix N coeffs powers k))
    (scale N (coeffs.getD (k+1) 0) powers[k+1]!)

/-- The proposed diagonal polynomial scaled by `p!`, evaluated in the same
finite cusp coefficient range by its listed integer coefficients. -/
def computedScaledClearedPrefix (p : ℕ) (coeffs : List ℤ) : List ℤ :=
  let N := 2*p+1
  let J := normalizedJCoefficientPrefix N
  scale N p.factorial (clearedPrefix N coeffs (prefixPowerTable N J (2*p)) (2*p))

open scoped PowerSeries

private theorem prefix_weaken {N M : ℕ} {xs : List ℤ} {A : ℤ⟦X⟧}
    (h : SeriesPrefix M xs A) (hm : N ≤ M) : SeriesPrefix N xs A := by
  intro i
  exact h ⟨i, i.isLt.trans_le hm⟩

private theorem prefix_take {N M : ℕ} {xs : List ℤ} {A : ℤ⟦X⟧}
    (h : SeriesPrefix M xs A) (hm : N ≤ M) : SeriesPrefix N (xs.take N) A := by
  intro i
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt, ← List.getD_eq_getElem?_getD]
  exact prefix_weaken h hm i

/-- The computable coefficient generator gives the initial coefficients
of the certified integral normalized modular invariant. -/
theorem normalizedJCoefficientPrefix_spec (N : ℕ) :
    SeriesPrefix N (normalizedJCoefficientPrefix N) integralNormalizedJExpansion := by
  let σ := ArithmeticFunction.sigma
  let a := read (N+1) fun n ↦ (σ 3 n : ℤ)
  let b := read (N+1) fun n ↦ (σ 5 n : ℤ)
  let t (n : ℕ) := (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)
  let linear := read (N+1) t
  let discr :=
    sub (N+1)
      (add (N+1) (add (N+1) linear (scale (N+1) 100 (pow (N+1) a 2)))
        (scale (N+1) 8000 (pow (N+1) a 3)))
      (scale (N+1) 147 (pow (N+1) b 2))
  let discrUnit := read N fun n ↦ discr.getD (n+1) 0
  let e4 := add N (read N fun n ↦ if n = 0 then 1 else 0) (scale N 240 a)
  have ha : SeriesPrefix (N+1) a (divisorPowerSeries 3) := of_mk _ _
  have hb : SeriesPrefix (N+1) b (divisorPowerSeries 5) := of_mk _ _
  have hlinear : SeriesPrefix (N+1) linear (PowerSeries.mk t) := of_mk _ _
  have hd : SeriesPrefix (N+1) discr integralDiscriminantExpansion := by
    have hh := sub_spec
      (add_spec (add_spec hlinear (scale_spec (pow_spec ha 2) 100))
        (scale_spec (pow_spec ha 3) 8000))
      (scale_spec (pow_spec hb 2) 147)
    change SeriesPrefix (N+1) discr
      (PowerSeries.mk t + 100 * divisorPowerSeries 3 ^ 2 + 8000 * divisorPowerSeries 3 ^ 3 -
        147 * divisorPowerSeries 5 ^ 2)
    simpa only [map_ofNat] using hh
  have hud : SeriesPrefix N discrUnit integralNormalizedDiscriminantExpansion := by
    intro i
    change (read N fun n ↦ discr.getD (n+1) 0).getD i 0 = _
    rw [getD_read, integralNormalizedDiscriminantExpansion, PowerSeries.coeff_mk]
    exact hd ⟨(i:ℕ)+1, Nat.succ_lt_succ i.isLt⟩
  have he : SeriesPrefix N e4 (1 + 240 * divisorPowerSeries 3) := by
    have hh := add_spec (const N 1) (scale_spec (prefix_weaken ha (Nat.le_succ N)) 240)
    simpa only [map_one, map_ofNat] using hh
  have hI := inverseUnit_spec hud constantCoeff_integralNormalizedDiscriminantExpansion
    (N.log2+1) Nat.lt_log2_self.le
  exact mul_spec (pow_spec he 3) hI

private theorem array_push_getElem!_lt {α : Type*} [Inhabited α] (a : Array α) (x : α)
    (i : ℕ) (hi : i < a.size) : (a.push x)[i]! = a[i]! := by
  have hi' : i < (a.push x).size := by simp only [Array.size_push]; omega
  rw [getElem!_pos (a.push x) i hi', getElem!_pos a i hi, Array.getElem_push_lt]

private theorem array_push_getElem!_last {α : Type*} [Inhabited α] (a : Array α) (x : α)
    (i : ℕ) (hi : i = a.size) : (a.push x)[i]! = x := by
  subst i
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

private theorem array_getElem!_singleton {α : Type*} [Inhabited α] (x : α) :
    (#[x])[0]! = x := by rfl

@[simp] private theorem prefixPowerTable_size (N : ℕ) (xs : List ℤ) (k : ℕ) :
    (prefixPowerTable N xs k).size = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [prefixPowerTable, Array.size_push, ih]

private theorem prefixPowerTable_spec {N : ℕ} {xs : List ℤ} {A : ℤ⟦X⟧}
    (h : SeriesPrefix N xs A) (k i : ℕ) (hi : i ≤ k) :
    SeriesPrefix N (prefixPowerTable N xs k)[i]! (A^i) := by
  induction k generalizing i with
  | zero =>
    have hf : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    simpa only [prefixPowerTable, array_getElem!_singleton, pow_zero, map_one] using const N 1
  | succ k ih =>
    rw [prefixPowerTable]
    by_cases hle : i ≤ k
    · have hi' : i < (prefixPowerTable N xs k).size := by
        rw [prefixPowerTable_size]
        exact Nat.lt_succ_of_le hle
      rw [array_push_getElem!_lt _ _ _ hi']
      exact ih i hle
    · have he : i = k+1 := by omega
      subst i
      rw [array_push_getElem!_last _ _ _ (prefixPowerTable_size N xs k).symm, pow_succ]
      exact mul_spec (ih k le_rfl) h

private theorem tracePowerPrefix_spec (p k : ℕ)
    {powers : Array (List ℤ)} {F : ℤ⟦X⟧}
    (h : SeriesPrefix (2*p*p+1) powers[k]! (F^k)) :
    SeriesPrefix (2*p+1) (tracePowerPrefix p k (2*p+1) powers) (heckeTraceSeries p k F) := by
  intro i
  simp only [tracePowerPrefix, getD_read, heckeTraceSeries, PowerSeries.coeff_mk]
  split_ifs
  · congr 1
    have hbound : p*(i : ℕ) < 2*p*p+1 := by
      have hh : (i : ℕ) ≤ 2*p := Nat.lt_succ_iff.mp i.isLt
      have hmul := Nat.mul_le_mul_left p hh
      nlinarith
    exact h ⟨p*i-(p-1)*k, (Nat.sub_le ..).trans_lt hbound⟩
  · rfl

private theorem getD_sumPrefixes (N : ℕ) (xs : List (List ℤ)) (i : Fin N) :
    (sumPrefixes N xs).getD i 0 = (xs.map fun t ↦ t.getD i 0).sum := by
  induction xs with
  | nil => rw [sumPrefixes, getD_read]; rfl
  | cons x xs ih => simp only [sumPrefixes, add, getD_read, ih, List.map_cons, List.sum_cons]

private theorem sumPrefixes_spec (N m : ℕ) (xs : Fin m → List ℤ) (F : Fin m → ℤ⟦X⟧)
    (h : ∀ j, SeriesPrefix N (xs j) (F j)) :
    SeriesPrefix N (sumPrefixes N (List.ofFn xs)) (∑ j, F j) := by
  intro i
  rw [getD_sumPrefixes, List.map_ofFn, List.sum_ofFn, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ h j i

@[simp] private theorem scaledElementaryTable_size (p N k : ℕ) (powers : Array (List ℤ)) :
    (scaledElementaryTable p N powers k).size = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [scaledElementaryTable, Array.size_push, ih]

private theorem scaledElementaryTable_spec (p : ℕ) (F : ℤ⟦X⟧) (powers : Array (List ℤ))
    (h : ∀ k ≤ p, SeriesPrefix (2*p*p+1) powers[k]! (F^k)) (k i : ℕ) (hk : k ≤ p) (hi : i ≤ k) :
    SeriesPrefix (2*p+1) (scaledElementaryTable p (2*p+1) powers k)[i]!
      (heckeScaledElementarySeries p F i) := by
  induction k generalizing i with
  | zero =>
    have hf : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    simpa only [scaledElementaryTable, array_getElem!_singleton, heckeScaledElementarySeries, map_one]
      using const (2*p+1) 1
  | succ k ih =>
    rw [scaledElementaryTable]
    by_cases hle : i ≤ k
    · have hi' : i < (scaledElementaryTable p (2*p+1) powers k).size := by
        rw [scaledElementaryTable_size]
        exact Nat.lt_succ_of_le hle
      rw [array_push_getElem!_lt _ _ _ hi']
      exact ih i (Nat.le_of_succ_le hk) hle
    · have he : i = k+1 := by omega
      subst i
      rw [array_push_getElem!_last _ _ _ (scaledElementaryTable_size p (2*p+1) k powers).symm,
        heckeScaledElementarySeries]
      have hterms (j : Fin (k+1)) :=
        scale_spec
          (mul_spec (ih j (Nat.le_of_succ_le hk) (Nat.le_of_lt_succ j.isLt))
            (tracePowerPrefix_spec p (k+1-j) (h _ ((Nat.sub_le _ _).trans hk))))
          ((-1 : ℤ) ^ (k+2+(j : ℕ)) * ↑(k.factorial / (j : ℕ).factorial))
      have hs := sumPrefixes_spec _ _ _ _ hterms
      convert hs using 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_pow, map_neg, map_one, pow_add]
      ring

/-- The integer computation implements the scaled formal diagonal
through the last coefficient required by the certificate. -/
theorem computedScaledDiagonalPrefix_spec (p : ℕ+) :
    SeriesPrefix (2*(p:ℕ)+1) (computedScaledDiagonalPrefix p)
      (heckeScaledDiagonalTraceSeries p integralNormalizedJExpansion) := by
  let m : ℕ := p
  let N := 2*m+1
  let M := 2*m*m+1
  let J := integralNormalizedJExpansion
  let jAll := normalizedJCoefficientPrefix M
  let jSmall := jAll.take N
  let powers := prefixPowerTable M jAll m
  let elementary := scaledElementaryTable m N powers m
  let smallPowers := prefixPowerTable N jSmall m
  have hM : N ≤ M := by
    have hm : 1 ≤ m := p.pos
    dsimp [N,M]
    nlinarith
  have hjAll : SeriesPrefix M jAll J := normalizedJCoefficientPrefix_spec M
  have hjSmall : SeriesPrefix N jSmall J := prefix_take hjAll hM
  have hPower (k : ℕ) (hk : k ≤ m) : SeriesPrefix M powers[k]! (J^k) :=
    prefixPowerTable_spec hjAll m k hk
  have hElem (k : ℕ) (hk : k ≤ m) :
      SeriesPrefix N elementary[k]! (heckeScaledElementarySeries m J k) :=
    scaledElementaryTable_spec m J powers hPower m k le_rfl hk
  have hSmall (k : ℕ) (hk : k ≤ m) : SeriesPrefix N smallPowers[k]! (J^k) :=
    prefixPowerTable_spec hjSmall m k hk
  have hterms (k : Fin (m+1)) :=
    scale_spec (mul_spec (hElem k (Nat.le_of_lt_succ k.isLt))
      (hSmall (m-k) (Nat.sub_le ..)))
      ((-1 : ℤ) ^ (k : ℕ) * ↑(m.factorial / (k : ℕ).factorial))
  have hs := sumPrefixes_spec N (m+1) _ _ hterms
  have hf := sub_spec (substitutePower_spec hjSmall m p.pos.ne') (shift_spec hjSmall (m-1))
  have h := mul_spec hf hs
  unfold heckeScaledDiagonalTraceSeries computedScaledDiagonalPrefix
  convert h using 1
  dsimp only
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, map_pow, map_neg, map_one]
  ring

private theorem clearedPrefix_spec (N n : ℕ) (coeffs : List ℤ) (powers : Array (List ℤ)) (A : ℤ⟦X⟧)
    (h : ∀ k ≤ n, SeriesPrefix N powers[k]! (A^k)) :
    SeriesPrefix N (clearedPrefix N coeffs powers n)
      (clearedIntegerPolynomialEvaluation (coefficientListPolynomial coeffs) A n) := by
  induction n with
  | zero =>
    simpa only [clearedPrefix, clearedIntegerPolynomialEvaluation, coeff_coefficientListPolynomial]
      using const N (coeffs.getD 0 0)
  | succ n ih =>
    rw [clearedPrefix, clearedIntegerPolynomialEvaluation, coeff_coefficientListPolynomial]
    simpa only [pow_one] using
      add_spec (shift_spec (ih fun k hk ↦ h k (hk.trans (Nat.le_succ _))) 1)
        (scale_spec (h (n+1) le_rfl) (coeffs.getD (n+1) 0))

/-- The proposed coefficient list is evaluated by the same cleared-series
identity used in the analytic comparison. -/
theorem computedScaledClearedPrefix_spec (p : ℕ) (coeffs : List ℤ) :
    SeriesPrefix (2*p+1) (computedScaledClearedPrefix p coeffs)
      (PowerSeries.C (p.factorial : ℤ) *
        clearedIntegerPolynomialEvaluation (coefficientListPolynomial coeffs)
          integralNormalizedJExpansion (2*p)) := by
  let N := 2*p+1
  let j := normalizedJCoefficientPrefix N
  let tab := prefixPowerTable N j (2*p)
  have hj := normalizedJCoefficientPrefix_spec N
  have ht (k : ℕ) (hk : k ≤ 2*p) := prefixPowerTable_spec hj (2*p) k hk
  exact scale_spec (clearedPrefix_spec N (2*p) coeffs tab integralNormalizedJExpansion ht)
    (p.factorial : ℤ)

end GRHArticle.SingularModuli
