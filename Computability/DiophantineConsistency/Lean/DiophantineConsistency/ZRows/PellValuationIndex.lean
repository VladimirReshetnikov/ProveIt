import DiophantineConsistency.ZRows.PellBinomial
import DiophantineConsistency.ArithmeticPellSquaredSeed
import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ZRows.ModelPellExistence
import DiophantineConsistency.ZRows.CoprimeSquares
import DiophantineConsistency.ZRows.Intersective19

/-! # The valuation inequality `v_p(n) ≤ v_p(ψ(n))` and the coprime split of a strong index

In every model `V` of `𝗜𝚺₁`, for the represented Pell ordinate `ψ(n) = ycoord n a` (base
`A = a + 2`, discriminant `Δ = delta a = A² − 1`; no parity of `A` is needed):

* `lift`: `k ∣ ψ(t) ⇒ k·ψ(t) ∣ ψ(k t)` (the gcd form of `ArithmeticPellSquaredSeed`);
* `frobenius_ordinate`: for an odd irreducible `p ∤ Δ`, `p ∣ ψ(p m) ⇒ p ∣ ψ(m)`, from the
  composition `ψ_A(p m) = ψ_A(m)·ψ_B(p)` (`B = χ_A(m)`, `ArithmeticPellCommonUnit.composition`)
  and the Frobenius form `ψ_B(p) ≡ Δ_B^((p−1)/2) (mod p)` (`ZRowsPellBinomial.ycoord_prime`);
* `index_valuation`: for irreducible `p` with `p ∣ ψ(n)`, `pᵏ ∣ n ⇒ pᵏ ∣ ψ(n)`. For `p = 2` and
  `p ∣ Δ` (where `p ∣ ψ(p)`) the hypothesis `p ∣ ψ(n)` is not even used;
* `coprime_split`: every `m ∣ n0` factors as `m = g·w` with `g ∣ I` and `w` coprime to `I`,
  whenever `I` satisfies the valuation inequality for `n0`, by order induction over prime-power
  splittings (`ZRowsIntersective19.valuation`);
* `strong_index`: for every `N > 0` there is `n0 > 0` with `N ∣ ψ(n0)`, together with the split
  `n0 = g·w`, `g ∣ ψ(n0)`, `Bez w ψ(n0) 1`. This is the input of the linear stepping of
  `ZRows/LinearInterpolation`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsPellValuation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellSquaredSeed ArithmeticPellCommonUnit
open ArithmeticPellIndexDivisibility ArithmeticPellClassification
open ModelFermat ZRowsPellBinomial ZRowsCoprimeSquares ZRowsIntersective19 ModelPellExistence

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord

/-! ### Elementary Pell facts -/

theorem two_le_x (a m : V) (hm : 0<m) : 2≤xcoord m a := by
  have h1 : 1≤ycoord m a := le_trans (pos_iff_one_le.mp hm) (time_le_y m a)
  have h := lt_iff_succ_le.mp (lt_of_le_of_lt h1 (ordinate_lt_abscissa a m))
  simpa only [one_add_one_eq_two] using h

theorem delta_shift (a m : V) (hm : 0<m) :
    delta (xcoord m a-2)=delta a*ycoord m a*ycoord m a := by
  have hx := two_le_x a m hm
  apply add_left_cancel (a := (1:V))
  calc
    1+delta (xcoord m a-2)=(xcoord m a-2+2)*(xcoord m a-2+2) := by unfold delta; ring
    _=xcoord m a*xcoord m a := by rw [tsub_add_cancel_of_le hx]
    _=1+delta a*ycoord m a*ycoord m a := norm m a

/-- Index divisibility `ψ(m) ∣ ψ(m k)`. -/
theorem y_dvd_mul (a m k : V) : ycoord m a∣ycoord (m*k) a := by
  rcases eq_zero_or_pos m with rfl|hm
  · simp
  · have hc := (composition (xcoord m a-2) a m
      (tsub_add_cancel_of_le (two_le_x a m hm)) k).2
    exact ⟨ycoord k (xcoord m a-2),by rw [← hc]; ring⟩

/-- **The gcd lift**: `k ∣ ψ(t) ⇒ k·ψ(t) ∣ ψ(k t)`. -/
theorem lift (a t k : V) (h : k∣ycoord t a) : k*ycoord t a∣ycoord (k*t) a := by
  obtain ⟨n,hk|hk⟩ := even_or_odd k
  · subst hk
    obtain ⟨r,s,-,hy⟩ := doubled_quotients n t a
    obtain ⟨q,hq⟩ := h
    rw [hy]
    refine ⟨xcoord t a+q*s,?_⟩
    calc
      2*n*xcoord t a*ycoord t a+ycoord t a*ycoord t a*s=
          2*n*xcoord t a*ycoord t a+ycoord t a*(2*n*q)*s := by rw [← hq]
      _=2*n*ycoord t a*(xcoord t a+q*s) := by ring
  · subst hk
    obtain ⟨s,hy⟩ := odd_quotient n t a
    obtain ⟨q,hq⟩ := h
    rw [hy]
    refine ⟨1+q*s,?_⟩
    calc
      (2*n+1)*ycoord t a+ycoord t a*ycoord t a*s=
          (2*n+1)*ycoord t a+ycoord t a*((2*n+1)*q)*s := by rw [← hq]
      _=(2*n+1)*ycoord t a*(1+q*s) := by ring

/-- `2` and the irreducible divisors of `Δ` divide their own ordinate. -/
theorem prime_dvd_y_self (a p : V) (h : p=2 ∨ p∣delta a) : p∣ycoord p a := by
  rcases h with rfl|h
  · rw [ArithmeticPellHalfIndex.y_two]
    exact ⟨a+2,rfl⟩
  · rcases quotient_alternatives a p with ⟨u,v,-,hy⟩|⟨u,v,-,hy⟩
    · rw [hy]
      exact dvd_add (dvd_mul_left p (a+2)) (dvd_mul_of_dvd_left h v)
    · rw [hy]
      exact dvd_add (dvd_refl p) (dvd_mul_of_dvd_left h v)

theorem power_dvd_y_power (a p : V) (hself : p∣ycoord p a) :
    ∀ k, power p k∣ycoord (power p k) a := by
  have C : ∀ k, power p (k+1)∣ycoord (power p (k+1)) a := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa using hself
    case succ k ih =>
      have hp : p∣ycoord (power p (k+1)) a := dvd_trans ⟨power p k,power_succ p k⟩ ih
      have hl := lift a (power p (k+1)) p hp
      rw [power_succ p (k+1)]
      exact dvd_trans (mul_dvd_mul_left p ih) hl
  intro k
  rcases zero_or_succ k with rfl|⟨j,rfl⟩
  · simp
  · exact C j

theorem lift_power (a t p : V) (hpt : p∣ycoord t a) :
    ∀ k, power p k*ycoord t a∣ycoord (power p k*t) a := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hpY : p∣ycoord (power p k*t) a := dvd_trans hpt (dvd_trans (dvd_mul_left _ _) ih)
    have hl := lift a (power p k*t) p hpY
    rw [power_succ,mul_assoc p (power p k) t,mul_assoc p (power p k) (ycoord t a)]
    exact dvd_trans (mul_dvd_mul_left p ih) hl

/-! ### Frobenius descent and the valuation inequality -/

/-- **Frobenius for the ordinate**: an odd irreducible `p ∤ Δ` with `p ∣ ψ(p m)` divides `ψ(m)`. -/
theorem frobenius_ordinate (a m p : V) (hp : Irred p) (hp2 : p≠2) (hpD : ¬ p∣delta a)
    (h : p∣ycoord (p*m) a) : p∣ycoord m a := by
  rcases eq_zero_or_pos m with rfl|hm
  · simp
  · have hc := (composition (xcoord m a-2) a m
      (tsub_add_cancel_of_le (two_le_x a m hm)) p).2
    rw [mul_comm p m,← hc] at h
    rcases hp.euclid h with h1|h1
    · have hd := dvd_delta_of_dvd_ycoord hp hp2 _ h1
      rw [delta_shift a m hm] at hd
      rcases hp.euclid hd with h2|h2
      · rcases hp.euclid h2 with h3|h3
        · exact absurd h3 hpD
        · exact h3
      · exact h2
    · exact h1

theorem descent (a t p : V) (hp : Irred p) (hp2 : p≠2) (hpD : ¬ p∣delta a) :
    ∀ k, p∣ycoord (power p k*t) a → p∣ycoord t a := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; simpa using h
  case succ k ih =>
    intro h
    rw [power_succ,mul_assoc] at h
    exact ih (frobenius_ordinate a _ p hp hp2 hpD h)

/-- **The valuation inequality**: `p ∣ ψ(n)` and `pᵏ ∣ n` give `pᵏ ∣ ψ(n)`. -/
theorem index_valuation (a n p k : V) (hp : Irred p) (hpn : p∣ycoord n a)
    (hk : power p k∣n) : power p k∣ycoord n a := by
  obtain ⟨t,rfl⟩ := hk
  by_cases hs : p=2 ∨ p∣delta a
  · exact dvd_trans (power_dvd_y_power a p (prime_dvd_y_self a p hs) k) (y_dvd_mul a _ t)
  · push_neg at hs
    have ht := descent a t p hp hs.1 hs.2 k hpn
    exact dvd_trans (dvd_mul_right _ _) (lift_power a t p ht k)

/-! ### The coprime split -/

/-- Every divisor of `n0` is a divisor of `I` times a unit modulo `I`, when `I` satisfies the
valuation inequality for `n0`. -/
theorem coprime_split (n0 I : V)
    (hval : ∀ p k : V, Irred p → p∣I → power p k∣n0 → power p k∣I) :
    ∀ m, 0<m → m∣n0 → ∃ g w : V, m=g*w ∧ g∣I ∧ Bez w I 1 := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · unfold Bez
    definability
  case ind m ih =>
    intro hm hmn
    rcases lt_or_eq_of_le (pos_iff_one_le.mp hm) with hm1|hm1
    · obtain ⟨p,hp1,hpm,hirr⟩ := exists_irred_dvd m hm1
      have hp : Irred p := ⟨hp1,hirr⟩
      obtain ⟨k,r,hk1,hmr,hpr⟩ := valuation hp hm hpm
      have hr0 : 0<r := by
        rcases eq_zero_or_pos r with h0|h0
        · rw [h0,mul_zero] at hmr
          exact absurd hmr hm.ne'
        · exact h0
      have h2P : 2≤power p k := by
        have := power_mono_exponent p 1 k hp.1.le hk1
        rw [power_one] at this
        exact le_trans (one_lt_iff_two_le.mp hp.1) this
      have hrm : r<m := by
        calc r<r+r := lt_add_of_pos_left r hr0
          _=2*r := (two_mul r).symm
          _≤power p k*r := mul_le_mul_of_nonneg_right h2P (Arithmetic.zero_le r)
          _=m := hmr.symm
      have hrn : r∣n0 := dvd_trans ⟨power p k,by rw [hmr]; ring⟩ hmn
      have hPn : power p k∣n0 := dvd_trans ⟨r,hmr⟩ hmn
      obtain ⟨g,w,hgw,hgI,hw⟩ := ih r hrm hr0 hrn
      by_cases hpI : p∣I
      · refine ⟨power p k*g,w,by rw [hmr,hgw]; ring,?_,hw⟩
        have hP : power p k∣I := hval p k hp hpI hPn
        have hpg : ¬ p∣g := fun h => hpr (dvd_trans h ⟨w,hgw⟩)
        have hb : Bez (power p k) g 1 := bez_power (bez_of_irred hirr hpg) k
        obtain ⟨α,β,hαβ⟩ := bez_one_iff_ring.mp hb
        have hh := dvd_mul_of_bez_ring (ι_dvd_iff.mpr hP) (ι_dvd_iff.mpr hgI) hαβ
        rw [← map_mul] at hh
        exact ι_dvd_iff.mp hh
      · refine ⟨g,power p k*w,by rw [hmr,hgw]; ring,hgI,?_⟩
        exact bez_mul (bez_power (bez_of_irred hirr hpI) k) hw
    · subst hm1
      exact ⟨1,1,by simp,one_dvd I,bez_one_iff_ring.mpr ⟨1,0,by simp⟩⟩

/-! ### The strong index -/

theorem delta_not_square (a : V) : ∀ s : V, s*s≠delta a := by
  intro s hs
  have hlow : (a+1)*(a+1)<delta a := by
    unfold delta
    exact mul_lt_mul_of_pos_left (by
      calc a+1<a+1+2 := lt_add_of_pos_right _ (by simp)
        _=a+3 := by ring) (by simp)
  have hhigh : delta a<(a+2)*(a+2) := by
    have he : delta a+1=(a+2)*(a+2) := by unfold delta; ring
    rw [← he]
    exact lt_add_one _
  rcases le_or_gt s (a+1) with h|h
  · have hle : s*s≤(a+1)*(a+1) := mul_le_mul h h (by simp) (by simp)
    exact absurd hs (ne_of_lt (lt_of_le_of_lt hle hlow))
  · have h2 : a+2≤s := by
      have := lt_iff_succ_le.mp h
      simpa only [add_assoc,one_add_one_eq_two] using this
    have hle : (a+2)*(a+2)≤s*s := mul_le_mul h2 h2 (by simp) (by simp)
    exact absurd hs (ne_of_gt (lt_of_lt_of_le hhigh hle))

/-- **A strong index with its coprime split**: `N ∣ ψ(n0)`, `n0 = g·w`, `g ∣ ψ(n0)`, and `w`
coprime to `ψ(n0)`. -/
theorem strong_index (a N : V) (hN : 0<N) :
    ∃ n0 g w : V, 0<n0 ∧ N∣ycoord n0 a ∧ n0=g*w ∧ g∣ycoord n0 a ∧ Bez w (ycoord n0 a) 1 := by
  have hd : 0<delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  obtain ⟨x,y,hy,hNy,hxy⟩ := exists_dvd (delta a) hd (delta_not_square a) N hN
  obtain ⟨n0,-,-,hn⟩ := solution_index a x y (by rw [hxy]; ring)
  have hn0 : 0<n0 := pos_iff_ne_zero.mpr (fun h0 => by
    rw [h0,y_zero] at hn
    exact (ne_of_gt hy) hn.symm)
  have hval : ∀ p k : V, Irred p → p∣ycoord n0 a → power p k∣n0 → power p k∣ycoord n0 a :=
    fun p k hp hpI hk => index_valuation a n0 p k hp hpI hk
  obtain ⟨g,w,hgw,hg,hw⟩ := coprime_split n0 (ycoord n0 a) hval n0 hn0 dvd_rfl
  exact ⟨n0,g,w,hn0,by rw [hn]; exact hNy,hgw,hg,hw⟩

#print axioms lift
#print axioms frobenius_ordinate
#print axioms index_valuation
#print axioms coprime_split
#print axioms strong_index

end DiophantineConsistency.ZRowsPellValuation
