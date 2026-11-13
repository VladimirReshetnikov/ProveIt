import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticBinomFactorial
import DiophantineConsistency.ArithmeticGcdNormalization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Gödel's beta function inside models of `𝗜𝚺₁`

For every `𝚺₁`-definable `s : V → V` and every `n` in a model `V` of `𝗜𝚺₁`
there are `a b` with `a % ((i+1)·b+1) = s i` for all `i ≤ n`
(`beta_exists`). This is the internal counterpart of the trace codes used by
`ScalarPRRepresentation.recursionCoordinates`.

The proof is the classical one, with every step internal:

* `exists_bound`: a common bound `M ≥ s i` for `i ≤ n` (Σ₁ induction);
* `b = (n+M)!`: then `s i < (i+1)·b+1`, and the moduli `(i+1)·b+1`, `i ≤ n`,
  are pairwise coprime (`moduli_bez`), using the gcd certificate of
  `ArithmeticGcdNormalization` and the cancellation `unit_certificate_cancel`;
* `crt_accumulate`: a Σ₁ induction on the number of prescribed residues. The
  step solves one new congruence with a Bezout identity evaluated in the ring of
  differences `DiffRing V`, and keeps the product of the used moduli coprime to
  every later modulus.

Coprimality is stated as a natural Bezout certificate `Bez x y 1`
(`∃ u v w z, 1 + x u + y v = x w + y z`), so every induction formula is a
`𝚺₁` formula of the model. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelBetaFunction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticBinomFactorial ArithmeticGcdNormalization

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Elementary facts -/

theorem beta_succ_pos (x : V) : 0 < x + 1 :=
  lt_of_lt_of_le _root_.zero_lt_one le_add_self

/-- A difference that is a ring multiple of `d` preserves the residue modulo `d`. -/
theorem mod_eq_of_sub_eq {x y d : V} {q : DiffRing V} (h : ι x - ι y = ι d * q) :
    x % d = y % d := by
  have key : ∀ {s t : V} (c : V), ι s = ι t + ι d * ι c → s % d = t % d := by
    intro s t c hst
    have he : s = t + d * c := ι_injective (by rw [map_add, map_mul]; exact hst)
    rcases eq_zero_or_pos d with hd | hd
    · rw [he, hd, zero_mul, add_zero]
    · rw [he, mod_add_mul' t c hd]
  rcases nonneg_or_nonpos q with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact key (s := x) (t := y) c (by linear_combination h)
  · exact (key (s := y) (t := x) c (by linear_combination (-1 : DiffRing V) * h)).symm

/-- A natural Bezout certificate for `1` is a ring identity in `DiffRing V`. -/
theorem bez_one_iff_ring {a b : V} :
    Bez a b 1 ↔ ∃ α β : DiffRing V, ι a * α + ι b * β = 1 := by
  constructor
  · rintro ⟨u, v, w, z, he⟩
    refine ⟨ι w - ι u, ι z - ι v, ?_⟩
    have h := congrArg (ι (V := V)) he
    simp only [map_add, map_mul, map_one] at h
    linear_combination (-1 : DiffRing V) * h
  · rintro ⟨α, β, h⟩
    obtain ⟨p, q, rfl⟩ := exists_mk α
    obtain ⟨r, s, rfl⟩ := exists_mk β
    rw [mk_eq_sub, mk_eq_sub] at h
    refine ⟨q, s, p, r, ι_injective ?_⟩
    simp only [map_add, map_mul, map_one]
    linear_combination (-1 : DiffRing V) * h

/-- Coprimality to `b` is closed under products. -/
theorem bez_mul {a a' b : V} (h : Bez a b 1) (h' : Bez a' b 1) : Bez (a * a') b 1 := by
  obtain ⟨α, β, hab⟩ := bez_one_iff_ring.mp h
  obtain ⟨α', β', hab'⟩ := bez_one_iff_ring.mp h'
  refine bez_one_iff_ring.mpr
    ⟨α * α', β * (ι a' * α') + ι a * α * β' + ι b * β * β', ?_⟩
  rw [map_mul]
  linear_combination (ι a' * α' + ι b * β') * hab + hab'

/-! ### Factorials -/

theorem le_fact (x : V) : x ≤ fact x := by
  rcases zero_or_succ x with rfl | ⟨y, rfl⟩
  · exact Arithmetic.zero_le _
  · rw [fact_succ]
    exact LO.FirstOrder.Arithmetic.le_mul_of_pos_right (fact_pos y)

/-- Every positive `d ≤ N` divides `N!`. -/
theorem dvd_fact_of_le (N : V) : ∀ d ≤ N, 0 < d → d ∣ fact N := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro d hd hpos
    exact absurd (lt_of_lt_of_le hpos hd) (_root_.lt_irrefl _)
  case succ N ih =>
    intro d hd hpos
    rw [fact_succ]
    rcases lt_or_eq_of_le hd with hlt | heq
    · exact Dvd.dvd.mul_left (ih d (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hlt) hpos) (N + 1)
    · rw [heq]
      exact dvd_mul_right (N + 1) (fact N)

/-! ### Bounds and moduli -/

/-- A common bound for the first `n+1` values of a `𝚺₁` function. -/
theorem exists_bound (s : V → V) [𝚺₁-Function₁[V] s] (n : V) :
    ∃ M : V, ∀ i ≤ n, s i ≤ M := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    refine ⟨s 0, fun i hi => ?_⟩
    have hi0 : i = 0 := nonpos_iff_eq_zero.mp hi
    subst hi0
    exact le_rfl
  case succ n ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨M + s (n + 1), fun i hi => ?_⟩
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact le_trans (hM i (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hlt)) le_self_add
    · rw [heq]
      exact le_add_self

/-- If every positive `d ≤ N` divides `b`, the moduli `(i+1)·b+1` with
`i < j ≤ N` are coprime. -/
theorem moduli_bez (b N i j : V) (hdiv : ∀ d ≤ N, 0 < d → d ∣ b) (hij : i < j)
    (hjN : j ≤ N) : Bez ((i + 1) * b + 1) ((j + 1) * b + 1) 1 := by
  obtain ⟨e, he⟩ := exists_add_of_le (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hij)
  obtain ⟨g, hgi, hgj, hbez⟩ := gcd_certificate_exists ((i + 1) * b + 1) ((j + 1) * b + 1)
  have hsplit : (j + 1) * b + 1 = ((i + 1) * b + 1) + (e + 1) * b := by
    rw [he]
    ring
  have hgpos : 0 < g := pos_iff_ne_zero.mpr (by
    rintro rfl
    exact (beta_succ_pos ((i + 1) * b)).ne' (zero_dvd_iff.mp hgi))
  have hge : g ∣ (e + 1) * b := by
    have h1 : ((i + 1) * b + 1 + (e + 1) * b) % g = ((e + 1) * b) % g :=
      mod_add_remove_left_of_dvd hgi hgpos
    rw [← hsplit, mod_eq_zero_iff_dvd.mpr hgj] at h1
    exact mod_eq_zero_iff_dvd.mp h1.symm
  have hunit : Bez b g 1 := by
    have ⟨c, hc⟩ := hgi
    exact ⟨i + 1, 0, 0, c, by rw [← hc]; ring⟩
  have hg1 : g ∣ e + 1 :=
    unit_certificate_cancel hunit (by rw [mul_comm b (e + 1)]; exact hge)
  have hej : e + 1 ≤ j := by
    rw [he]
    calc e + 1 ≤ e + 1 + i := le_self_add
      _ = i + 1 + e := by ring
  have hgb : g ∣ b := dvd_trans hg1 (hdiv (e + 1) (le_trans hej hjN) (beta_succ_pos e))
  have hg_one : g = 1 := by
    have h2 : ((i + 1) * b + 1) % g = 1 % g :=
      mod_add_remove_left_of_dvd (Dvd.dvd.mul_left hgb (i + 1)) hgpos
    rw [mod_eq_zero_iff_dvd.mpr hgi] at h2
    exact LO.FirstOrder.Arithmetic.dvd_one_iff.mp (mod_eq_zero_iff_dvd.mp h2.symm)
  rw [hg_one] at hbez
  exact hbez

/-! ### Chinese remainder accumulation -/

set_option maxHeartbeats 4000000 in
/-- After `m` steps the first `m` residues are prescribed, the used moduli divide
the accumulated modulus `P`, and `P` is coprime to every later modulus. -/
theorem crt_accumulate (s : V → V) [𝚺₁-Function₁[V] s] (n b : V)
    (hcop : ∀ i j, i < j → j ≤ n → Bez ((i + 1) * b + 1) ((j + 1) * b + 1) 1)
    (hsmall : ∀ i ≤ n, s i < (i + 1) * b + 1) (m : V) :
    m ≤ n + 1 → ∃ a P : V, 0 < P ∧ (∀ i < m, a % ((i + 1) * b + 1) = s i) ∧
      (∀ i < m, (i + 1) * b + 1 ∣ P) ∧
      ∀ j ≤ n, m ≤ j → ∃ u v w z : V,
        1 + P * u + ((j + 1) * b + 1) * v = P * w + ((j + 1) * b + 1) * z := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    refine ⟨0, 1, _root_.zero_lt_one, fun i hi => absurd hi (not_lt.mpr (Arithmetic.zero_le i)),
      fun i hi => absurd hi (not_lt.mpr (Arithmetic.zero_le i)), fun j _ _ => ⟨0, 0, 1, 0, by ring⟩⟩
  case succ m ih =>
    intro hm1
    have hmn : m ≤ n := (add_le_add_iff_right 1).mp hm1
    obtain ⟨a, P, hP, hres, hdvd, hbez⟩ := ih (le_trans hmn le_self_add)
    obtain ⟨α, β, hαβ⟩ :=
      (bez_one_iff_ring (a := P) (b := (m + 1) * b + 1)).mp (hbez m hmn le_rfl)
    obtain ⟨K, hK⟩ := nonneg_iff.mp (abs_nonneg (ι P * α * (ι (s m) - ι a)))
    have hPM : (1 : DiffRing V) ≤ ι P * ι ((m + 1) * b + 1) := by
      have h1 : (1 : V) ≤ P * ((m + 1) * b + 1) :=
        pos_iff_one_le.mp (mul_pos hP (beta_succ_pos _))
      calc (1 : DiffRing V) = ι 1 := (map_one (ι (V := V))).symm
        _ ≤ ι (P * ((m + 1) * b + 1)) := ι_le_ι.mpr h1
        _ = ι P * ι ((m + 1) * b + 1) := map_mul (ι (V := V)) _ _
    have hK0 : (0 : DiffRing V) ≤ ι K := ι_nonneg K
    have hKle : ι K ≤ ι P * ι ((m + 1) * b + 1) * ι K := le_mul_of_one_le_left hK0 hPM
    have habs : -(ι P * α * (ι (s m) - ι a)) ≤ ι K := by
      rw [← hK]
      exact neg_le_abs _
    have ha0 : (0 : DiffRing V) ≤ ι a := ι_nonneg a
    obtain ⟨a', ha'⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤
        ι a + ι P * α * (ι (s m) - ι a) + ι P * ι ((m + 1) * b + 1) * ι K by linarith)
    refine ⟨a', P * ((m + 1) * b + 1), mul_pos hP (beta_succ_pos _), ?_, ?_, ?_⟩
    · intro i hi
      rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hi) with hlt | heq
      · obtain ⟨c, hc⟩ := hdvd i hlt
        rw [← hres i hlt]
        apply mod_eq_of_sub_eq
          (q := ι c * (α * (ι (s m) - ι a) + ι ((m + 1) * b + 1) * ι K))
        rw [← ha', hc, map_mul]
        ring
      · rw [heq]
        refine (mod_eq_of_sub_eq (q := β * (ι a - ι (s m)) + ι P * ι K) ?_).trans
          (mod_eq_self_of_lt (hsmall m hmn))
        rw [← ha']
        linear_combination (ι (s m) - ι a) * hαβ
    · intro i hi
      rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hi) with hlt | heq
      · exact Dvd.dvd.mul_right (hdvd i hlt) _
      · rw [heq]
        exact dvd_mul_left _ _
    · intro j hj hmj
      exact bez_mul (hbez j hj (le_trans le_self_add hmj))
        (hcop m j (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hmj) hj)

/-! ### The beta function -/

/-- Gödel's beta function: every internal `𝚺₁` sequence of length `n+1` has a
code `(a,b)` with entries `a % ((i+1)·b+1)`. -/
theorem beta_exists (s : V → V) [𝚺₁-Function₁[V] s] (n : V) :
    ∃ a b : V, ∀ i ≤ n, a % ((i + 1) * b + 1) = s i := by
  obtain ⟨M, hM⟩ := exists_bound s n
  have hdiv : ∀ d ≤ n + M, 0 < d → d ∣ fact (n + M) := dvd_fact_of_le (n + M)
  have hcop : ∀ i j, i < j → j ≤ n →
      Bez ((i + 1) * fact (n + M) + 1) ((j + 1) * fact (n + M) + 1) 1 :=
    fun i j hij hj => moduli_bez (fact (n + M)) (n + M) i j hdiv hij (le_trans hj le_self_add)
  have hsmall : ∀ i ≤ n, s i < (i + 1) * fact (n + M) + 1 := by
    intro i hi
    have h1 : s i ≤ fact (n + M) := le_trans (hM i hi) (le_trans le_add_self (le_fact (n + M)))
    have h2 : fact (n + M) ≤ (i + 1) * fact (n + M) :=
      LO.FirstOrder.Arithmetic.le_mul_of_pos_left (beta_succ_pos i)
    exact LO.FirstOrder.Arithmetic.lt_succ_iff_le.mpr (le_trans h1 h2)
  obtain ⟨a, P, _, hres, _, _⟩ :=
    crt_accumulate s n (fact (n + M)) hcop hsmall (n + 1) le_rfl
  exact ⟨a, fact (n + M), fun i hi => hres i (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mpr hi)⟩

end DiophantineConsistency.ModelBetaFunction
