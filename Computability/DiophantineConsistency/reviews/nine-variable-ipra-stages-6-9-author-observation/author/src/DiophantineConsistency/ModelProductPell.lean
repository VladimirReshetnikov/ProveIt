import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ArithmeticPellStrongDivisibility
import DiophantineConsistency.ArithmeticPellPigeonhole

/-! # Jones 1982, Lemma 2.27 inside every model of `𝗜𝚺₁`

Externally (`Diophantine.Paper1982.ProductPell`, `Jones1982.lemma_2_27`) the
lemma says: for `1 < A`, `1 < B ≤ C`, and either `2B ≤ C` or `B` odd, the
relation `C = ψ_A(B)` holds iff the system (A1)–(A7) has positive witnesses
`i, j`, for an arbitrary fixed positive `J`; (A1) is the single product-square
condition `D F I = □` together with `H ≡ C (mod F)`.

Here the same statement is proved in an arbitrary model `V` of `𝗜𝚺₁`, with all
indices internal (possibly nonstandard). The Pell sequences are the represented
`xcoord t b`, `ycoord t b` of `ArithmeticPellRecurrence`, i.e. `χ_A(t)`,
`ψ_A(t)` for the base `A = b + 2`; this offset makes `A² − 1 = delta b` a
subtraction-free polynomial and `1 < A` automatic. The congruence
`H ≡ C (mod F)` is `H % F = C % F` in `V`, and the square condition is
`∃ r, D * F * I = r * r`.

The proof mirrors the external one:

* **sufficiency** (`psi_of_ProductPellConds`): the three factors `D, F, I` are
  pairwise coprime (Bézout certificates from `F ≡ 1 (mod D)`, `I ≡ 1 (mod D)`
  and `I ≡ D (mod F)`), so each is a square (`pp_square_of_coprime`, via the
  internal gcd); the Pell classification gives indices `t₀, t', t''`; base
  transfer `ψ_A ≡ ψ_G (mod F)` and the hypothesis `H ≡ C (mod F)` give
  `ψ(t'') ≡ ψ(t₀) (mod χ(t'))`. Instead of the `ψ` step-down lemma (not in the
  internal toolkit) we pass to `χ(2t'') ≡ χ(2t₀) (mod χ(t'))` and apply
  `ArithmeticPellResidueClasses.doubled_step_down`, then reduce modulo
  `C ∣ t'`. The extra residue `B + t₀ = C` is excluded by `2B ≤ C` (which here
  forces `B = t₀`, using `2 t₀ ≤ ψ(t₀)`) or by parity (`ψ(t) ≡ t mod 2`);
* **necessity** (`exists_ProductPellConds`): the witnesses are built inside
  `V` from the internal pigeonhole lemma `ArithmeticPellPigeonhole.ordinate_dvd`
  (some positive `t'` with `J D C² ∣ ψ(t')`) and Pell solutions at the
  (possibly nonstandard) indices `B` and `t'`.

No `Paper1982`/`Diophantine` module is imported: those depend on the Mathlib
tactic umbrella, which is incompatible with the Foundation import surface. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelProductPell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Congruence and order bookkeeping -/

theorem pp_mod_add {m a a' c c' : V} (hm : 0 < m)
    (h1 : a % m = a' % m) (h2 : c % m = c' % m) : (a + c) % m = (a' + c') % m := by
  rw [mod_add hm, mod_add (a := a') hm, h1, h2]

theorem pp_mod_mul {m a a' c c' : V} (hm : 0 < m)
    (h1 : a % m = a' % m) (h2 : c % m = c' % m) : (a * c) % m = (a' * c') % m := by
  rw [mod_mul hm, mod_mul (a := a') hm, h1, h2]

/-- A residue `1` modulo `n > 1` is an explicit quotient form. -/
theorem pp_eq_one_add_of_mod (x n : V) (hn : 1 < n) (h : x % n = 1 % n) :
    x = 1 + n * (x / n) := by
  have h1 : (1 : V) % n = 1 := mod_eq_self_of_lt hn
  have h2 : n * (x / n) + x % n = x := div_add_mod x n
  rw [h, h1] at h2
  calc x = n * (x / n) + 1 := h2.symm
    _ = 1 + n * (x / n) := add_comm _ _

/-- The literal (A2)/(A4)/(A7) shape is the subtraction-free Pell norm. -/
theorem pp_norm_of_literal (b X Y : V) (h : X + Y * Y = (b + 2) * (b + 2) * Y * Y + 1) :
    X = 1 + delta b * Y * Y := by
  have h' : X + Y * Y = (1 + delta b * Y * Y) + Y * Y := by
    rw [h]; unfold delta; ring
  exact add_right_cancel h'

theorem pp_base_le_delta (b : V) : b + 2 ≤ delta b := by
  unfold delta
  exact le_trans (_root_.add_le_add (le_refl b) (by norm_num : (2 : V) ≤ 3))
    (le_mul_of_one_le_left (Arithmetic.zero_le _) (by simp : (1 : V) ≤ b + 1))

theorem pp_le_mul_sq (x C : V) (hC : 0 < C) : x ≤ x * C * C := by
  have h1 : 1 ≤ C := pos_iff_one_le.mp hC
  exact le_trans (le_mul_of_one_le_right (Arithmetic.zero_le x) h1)
    (le_mul_of_one_le_right (Arithmetic.zero_le (x * C)) h1)

theorem pp_base_le_CD (b C D : V) (hC : 0 < C) (hD : D = 1 + delta b * C * C) :
    b + 2 ≤ C * D := by
  have h1 : b + 2 ≤ D := by
    rw [hD]
    exact le_trans (le_trans (pp_base_le_delta b) (pp_le_mul_sq (delta b) C hC))
      (by simp : delta b * C * C ≤ 1 + delta b * C * C)
  exact le_trans h1 (le_mul_of_one_le_left (Arithmetic.zero_le D) (pos_iff_one_le.mp hC))

theorem pp_lt_two_mul (x : V) (hx : 0 < x) : x < 2 * x := by
  calc x < x + x := lt_add_of_pos_right x hx
    _ = 2 * x := (two_mul x).symm

/-- `2p ≤ ψ_A(p)` for every internal `p ≥ 2`. -/
theorem pp_two_mul_le_y (a p : V) (hp : 2 ≤ p) : 2 * p ≤ ycoord p a := by
  rcases hp.eq_or_lt with h | h
  · rw [← h, ArithmeticPellHalfIndex.y_two]
    exact mul_le_mul_of_nonneg_left (by simp : (2 : V) ≤ a + 2) (by simp : (0 : V) ≤ 2)
  · have h3 : 3 ≤ p := by
      have h' := lt_iff_succ_le.mp h
      rwa [show (2 : V) + 1 = 3 by ring] at h'
    exact le_of_lt (ArithmeticPellHalfIndex.twice_index_lt_y a p h3)

/-! ### Two Pell facts by internal induction -/

/-- Base transfer: if `b + 2 ≡ g + 2 (mod m)` then both Pell coordinates agree
modulo `m` at every internal index (`xy_modEq_of_modEq` externally). -/
theorem pp_base_transfer (b g m : V) (hm : 0 < m) (hbase : (b + 2) % m = (g + 2) % m)
    (t : V) :
    xcoord t b % m = xcoord t g % m ∧ ycoord t b % m = ycoord t g % m := by
  have hdelta : delta b % m = delta g % m := by
    apply ArithmeticPellResidueClasses.mod_add_cancel _ _ 1 _ hm
    have e1 : delta b + 1 = (b + 2) * (b + 2) := by unfold delta; ring
    have e2 : delta g + 1 = (g + 2) * (g + 2) := by unfold delta; ring
    rw [e1, e2]
    exact pp_mod_mul hm hbase hbase
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ t ih =>
    rw [x_succ, x_succ, y_succ, y_succ]
    exact ⟨pp_mod_add hm (pp_mod_mul hm hbase ih.1) (pp_mod_mul hm hdelta ih.2),
      pp_mod_add hm ih.1 (pp_mod_mul hm hbase ih.2)⟩

/-- Parity: `ψ_A(t) + t` is even (`yn_modEq_two` externally), carried together
with the oddness of `χ_A(t) + (A − 1) ψ_A(t)`. -/
theorem pp_parity (b t : V) :
    (∃ q : V, ycoord t b + t = 2 * q) ∧
      (∃ r : V, xcoord t b + (b + 1) * ycoord t b = 2 * r + 1) := by
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  case succ t ih =>
    obtain ⟨⟨q, hq⟩, ⟨r, hr⟩⟩ := ih
    refine ⟨⟨r + q + 1, ?_⟩, ⟨(b + 1) * xcoord t b + r + (b + 1) * (b + 2) * ycoord t b, ?_⟩⟩
    · rw [y_succ]
      calc xcoord t b + (b + 2) * ycoord t b + (t + 1)
          = (xcoord t b + (b + 1) * ycoord t b) + (ycoord t b + t) + 1 := by ring
        _ = (2 * r + 1) + 2 * q + 1 := by rw [hr, hq]
        _ = 2 * (r + q + 1) := by ring
    · rw [x_succ, y_succ]
      calc (b + 2) * xcoord t b + delta b * ycoord t b +
            (b + 1) * (xcoord t b + (b + 2) * ycoord t b)
          = 2 * ((b + 1) * xcoord t b) + 2 * ((b + 1) * (b + 2) * ycoord t b) +
              (xcoord t b + (b + 1) * ycoord t b) := by unfold delta; ring
        _ = 2 * ((b + 1) * xcoord t b) + 2 * ((b + 1) * (b + 2) * ycoord t b) +
              (2 * r + 1) := by rw [hr]
        _ = 2 * ((b + 1) * xcoord t b + r + (b + 1) * (b + 2) * ycoord t b) + 1 := by ring

/-- A `ψ` congruence gives a `χ` congruence at doubled indices:
`χ(2u) + 1 = 2 + 2 δ ψ(u)²`. -/
theorem pp_double_x_mod (b s t m : V) (hm : 0 < m)
    (h : ycoord s b % m = ycoord t b % m) :
    xcoord (2 * s) b % m = xcoord (2 * t) b % m := by
  apply ArithmeticPellResidueClasses.mod_add_cancel _ _ 1 _ hm
  have e : ∀ u : V, xcoord (2 * u) b + 1 = 2 + 2 * delta b * (ycoord u b * ycoord u b) := by
    intro u
    calc xcoord (2 * u) b + 1 = 2 * xcoord u b * xcoord u b :=
          ArithmeticPellPeriodicity.double_x_add_one u b
      _ = 2 * (xcoord u b * xcoord u b) := by ring
      _ = 2 * (1 + delta b * ycoord u b * ycoord u b) := by
          rw [ArithmeticPellRecurrence.norm]
      _ = 2 + 2 * delta b * (ycoord u b * ycoord u b) := by ring
  rw [e s, e t]
  exact pp_mod_add hm rfl (pp_mod_mul hm rfl (pp_mod_mul hm h h))

/-! ### Bézout certificates and coprime square factors -/

theorem pp_bez_symm {a c g : V} (h : Bez a c g) : Bez c a g := by
  obtain ⟨u, v, w, z, he⟩ := h
  refine ⟨v, u, z, w, ?_⟩
  simpa only [add_assoc, add_comm, add_left_comm] using he

theorem pp_bez_one_add (n k : V) : Bez n (1 + n * k) 1 :=
  ⟨k, 0, 0, 1, by ring⟩

/-- A unit certificate for `(D, F)` transfers to any `I ≡ D (mod F)`. -/
theorem pp_bez_transfer {D F I k k' r : V} (h : Bez D F 1)
    (hD : D = F * k' + r) (hI : I = F * k + r) : Bez I F 1 := by
  obtain ⟨u, v, w, z, he⟩ := h
  rw [hD] at he
  refine ⟨u, k' * u + v + k * w, w, k' * w + z + k * u, ?_⟩
  rw [hI]
  calc 1 + (F * k + r) * u + F * (k' * u + v + k * w)
      = (1 + (F * k' + r) * u + F * v) + F * k * u + F * k * w := by ring
    _ = ((F * k' + r) * w + F * z) + F * k * u + F * k * w := by rw [he]
    _ = (F * k + r) * w + F * (k' * w + z + k * u) := by ring

/-- A factor of a square that has a unit certificate with its cofactor is a
square (`IsSquare.of_coprime_mul` externally), via the internal gcd. -/
theorem pp_square_of_coprime (a c r : V) (hu : Bez a c 1) (h : a * c = r * r) :
    ∃ s : V, a = s * s := by
  obtain ⟨g, hg⟩ := gcd_certificate_exists a r
  obtain ⟨a', ha⟩ := hg.1
  obtain ⟨r', hr⟩ := hg.2.1
  by_cases hg0 : g = 0
  · exact ⟨0, by rw [ha, hg0]; simp⟩
  have hgpos : 0 < g := pos_iff_ne_zero.mpr hg0
  obtain ⟨u, v, w, z, he⟩ := hg.2.2
  have hunit : Bez a' r' 1 := by
    refine ⟨u, v, w, z, ?_⟩
    apply mul_left_cancel₀ (ne_of_gt hgpos)
    calc g * (1 + a' * u + r' * v) = g + a * u + r * v := by rw [ha, hr]; ring
      _ = a * w + r * z := he
      _ = g * (a' * w + r' * z) := by rw [ha, hr]; ring
  have hkey : a' * c = g * (r' * r') := by
    apply mul_left_cancel₀ (ne_of_gt hgpos)
    calc g * (a' * c) = a * c := by rw [ha]; ring
      _ = r * r := h
      _ = g * (g * (r' * r')) := by rw [hr]; ring
  have hbz : Bez r' a' 1 := pp_bez_symm hunit
  have h1 : a' ∣ r' * (r' * g) := ⟨c, by rw [hkey]; ring⟩
  have h2 : a' ∣ r' * g := unit_certificate_cancel hbz h1
  have h3 : a' ∣ g := unit_certificate_cancel hbz h2
  have hgc : Bez g c 1 := by
    obtain ⟨u1, v1, w1, z1, he1⟩ := hu
    refine ⟨a' * u1, v1, a' * w1, z1, ?_⟩
    calc 1 + g * (a' * u1) + c * v1 = 1 + a * u1 + c * v1 := by rw [ha]; ring
      _ = a * w1 + c * z1 := he1
      _ = g * (a' * w1) + c * z1 := by rw [ha]; ring
  have h4 : g ∣ c * a' := ⟨r' * r', by rw [mul_comm c a', hkey]⟩
  have h5 : g ∣ a' := unit_certificate_cancel (pp_bez_symm hgc) h4
  have hag : a' = g := Arithmetic.dvd_antisymm h3 h5
  exact ⟨g, by rw [ha, hag]⟩

/-! ### The system (A1)–(A7) -/

/-- The literal polynomial system (A1)–(A7) of Lemma 2.27, in `V`'s natural
arithmetic: negative terms are moved across, the square is `∃ r, DFI = r²` and
the congruence `F ∣ H − C` is `H % F = C % F`. -/
structure ProductPellConds (A B C J i j D E F G H I : V) : Prop where
  square : ∃ r : V, D * F * I = r * r
  congr : H % F = C % F
  A2 : D + C * C = A * A * C * C + 1
  A3 : E = i * J * D * C * C
  A4 : F + E * E = A * A * E * E + 1
  A5 : G + F * A = A + F * (C * D + 1)
  A6 : H = B + j * C
  A7 : I + H * H = G * G * H * H + 1

set_option maxHeartbeats 1000000 in
/-- Sufficiency of the product-square Pell system, in every model of `𝗜𝚺₁`. -/
theorem psi_of_ProductPellConds (b B C J i j D E F G H I : V)
    (hB : 1 < B) (hBC : B ≤ C) (hpar : 2 * B ≤ C ∨ B % 2 = 1) (hJ : 0 < J) (hi : 0 < i)
    (hS : ProductPellConds (b + 2) B C J i j D E F G H I) : C = ycoord B b := by
  obtain ⟨⟨r, hsq⟩, hHC, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hS
  -- sizes
  have hB2 : 2 ≤ B := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hB
  have hC2 : 2 ≤ C := le_trans hB2 hBC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : V) < 2) hC2
  have hD : D = 1 + delta b * C * C := pp_norm_of_literal b D C hA2
  have hF : F = 1 + delta b * E * E := pp_norm_of_literal b F E hA4
  have hDpos : 0 < D := by
    rw [hD]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * C * C)
  have hFpos : 0 < F := by
    rw [hF]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * E * E)
  have hEpos : 0 < E := by
    rw [hA3]
    exact mul_pos (mul_pos (mul_pos (mul_pos hi hJ) hDpos) hCpos) hCpos
  have hDC1 : 1 < D * C :=
    lt_of_lt_of_le (by norm_num : (1 : V) < 2)
      (le_trans hC2 (le_mul_of_one_le_left (Arithmetic.zero_le C) (pos_iff_one_le.mp hDpos)))
  have hDCpos : 0 < D * C := lt_trans (by norm_num : (0 : V) < 1) hDC1
  have hAle : b + 2 ≤ C * D + 1 :=
    le_trans (pp_base_le_CD b C D hCpos hD) (by simp : C * D ≤ C * D + 1)
  -- `F ≡ 1 (mod DC)`
  obtain ⟨q, hFq⟩ : ∃ q : V, F = 1 + D * C * q := by
    refine ⟨delta b * i * J * C * E, ?_⟩
    calc F = 1 + delta b * E * E := hF
      _ = 1 + delta b * E * (i * J * D * C * C) := by rw [← hA3]
      _ = 1 + D * C * (delta b * i * J * C * E) := by ring
  have hFD : F = 1 + D * (C * q) := by rw [hFq]; ring
  -- `G ≡ 1 (mod DC)`
  have hGlin : G + D * C * (q * (b + 2)) = 1 + D * C * (F + q) := by
    have h : G + D * C * (q * (b + 2)) + (b + 2) = 1 + D * C * (F + q) + (b + 2) := by
      calc G + D * C * (q * (b + 2)) + (b + 2) = G + (1 + D * C * q) * (b + 2) := by ring
        _ = G + F * (b + 2) := by rw [← hFq]
        _ = b + 2 + F * (C * D + 1) := hA5
        _ = b + 2 + F * (C * D) + (1 + D * C * q) := by rw [← hFq]; ring
        _ = 1 + D * C * (F + q) + (b + 2) := by ring
    exact add_right_cancel h
  have hGmod : G % (D * C) = 1 % (D * C) := by
    have h : (G + D * C * (q * (b + 2))) % (D * C) = (1 + D * C * (F + q)) % (D * C) := by
      rw [hGlin]
    rwa [mod_add_mul' G (q * (b + 2)) hDCpos, mod_add_mul' 1 (F + q) hDCpos] at h
  obtain ⟨m, hGm⟩ : ∃ m : V, G = 1 + D * C * m :=
    ⟨G / (D * C), pp_eq_one_add_of_mod G (D * C) hDC1 hGmod⟩
  -- `G ≥ 2`, so `G` is a Pell base `g + 2`
  have hG2 : 2 ≤ G := by
    by_contra hn
    have hGlt : G < 2 := not_le.mp hn
    have hFmul : F * (b + 2) ≤ F * (C * D + 1) :=
      mul_le_mul_of_nonneg_left hAle (Arithmetic.zero_le F)
    have hlt : G + F * (b + 2) < b + 2 + F * (C * D + 1) :=
      lt_of_lt_of_le (add_lt_add_of_lt_of_le hGlt (le_refl (F * (b + 2))))
        (_root_.add_le_add (by simp : (2 : V) ≤ b + 2) hFmul)
    rw [hA5] at hlt
    exact _root_.lt_irrefl _ hlt
  obtain ⟨g, hGg⟩ : ∃ g : V, G = g + 2 := ⟨G - 2, (tsub_add_cancel_of_le hG2).symm⟩
  have hI : I = 1 + delta g * H * H := pp_norm_of_literal g I H (by rw [← hGg]; exact hA7)
  -- `I ≡ 1 (mod D)`
  have hID0 : I = 1 + D * ((2 * C * m + D * C * C * m * m) * H * H) := by
    have h : I + H * H = (1 + D * ((2 * C * m + D * C * C * m * m) * H * H)) + H * H := by
      rw [hA7, hGm]; ring
    exact add_right_cancel h
  obtain ⟨kI, hID⟩ : ∃ k : V, I = 1 + D * k := ⟨_, hID0⟩
  -- `I ≡ D (mod F)`
  have hGF : G % F = (b + 2) % F := by
    have h : (G + F * (b + 2)) % F = (b + 2 + F * (C * D + 1)) % F := by rw [hA5]
    rwa [mod_add_mul' G (b + 2) hFpos, mod_add_mul' (b + 2) (C * D + 1) hFpos] at h
  have hHHF : (H * H) % F = (C * C) % F := pp_mod_mul hFpos hHC hHC
  have hGGF : (G * G * H * H) % F = ((b + 2) * (b + 2) * C * C) % F :=
    pp_mod_mul hFpos (pp_mod_mul hFpos (pp_mod_mul hFpos hGF hGF) hHC) hHC
  have hIF : I % F = D % F := by
    apply ArithmeticPellResidueClasses.mod_add_cancel I D (C * C) F hFpos
    calc (I + C * C) % F = (I + H * H) % F := pp_mod_add hFpos rfl hHHF.symm
      _ = (G * G * H * H + 1) % F := by rw [hA7]
      _ = ((b + 2) * (b + 2) * C * C + 1) % F := pp_mod_add hFpos hGGF rfl
      _ = (D + C * C) % F := by rw [hA2]
  -- pairwise unit certificates
  have bDF : Bez D F 1 := by rw [hFD]; exact pp_bez_one_add D (C * q)
  have bDFI : Bez D (F * I) 1 := by
    have h : F * I = 1 + D * (C * q + kI + D * (C * q) * kI) := by rw [hFD, hID]; ring
    rw [h]; exact pp_bez_one_add D _
  have bIF : Bez I F 1 := by
    have hI' : I = F * (I / F) + D % F := by
      calc I = F * (I / F) + I % F := (div_add_mod I F).symm
        _ = F * (I / F) + D % F := by rw [hIF]
    exact pp_bez_transfer bDF (div_add_mod D F).symm hI'
  have bFI : Bez F I 1 := pp_bez_symm bIF
  -- each factor is a square
  obtain ⟨s, hDs⟩ := pp_square_of_coprime D (F * I) r bDFI (by rw [← hsq]; ring)
  obtain ⟨r1, hr1⟩ := pp_square_of_coprime (F * I) D r (pp_bez_symm bDFI) (by rw [← hsq]; ring)
  obtain ⟨f, hFf⟩ := pp_square_of_coprime F I r1 bFI hr1
  obtain ⟨u, hIu⟩ := pp_square_of_coprime I F r1 bIF (by rw [← hr1]; ring)
  -- Pell indices
  obtain ⟨t₀, -, -, hyt₀⟩ :=
    ArithmeticPellClassification.solution_index b s C (by rw [← hDs]; exact hD)
  obtain ⟨t', -, hxt', hyt'⟩ :=
    ArithmeticPellClassification.solution_index b f E (by rw [← hFf]; exact hF)
  obtain ⟨t'', -, -, hyt''⟩ :=
    ArithmeticPellClassification.solution_index g u H (by rw [← hIu]; exact hI)
  -- the index `t₀`
  have hy1 : ycoord 1 b = 1 := by simpa using y_succ (0 : V) b
  have ht₀pos : 0 < t₀ := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0, y_zero] at hyt₀
    rw [← hyt₀] at hC2
    exact absurd hC2 (by norm_num)
  have ht₀2 : 2 ≤ t₀ := by
    have hne1 : t₀ ≠ 1 := by
      intro h1
      rw [h1, hy1] at hyt₀
      rw [← hyt₀] at hC2
      exact absurd hC2 (by norm_num)
    have h1lt : 1 < t₀ := lt_of_le_of_ne (pos_iff_one_le.mp ht₀pos) (Ne.symm hne1)
    simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp h1lt
  have h2t₀ : 2 * t₀ ≤ C := by rw [← hyt₀]; exact pp_two_mul_le_y b t₀ ht₀2
  have ht₀C : t₀ < C := lt_of_lt_of_le (pp_lt_two_mul t₀ ht₀pos) h2t₀
  -- the index `t'`: `C ∣ t'`
  have ht'pos : 0 < t' := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0, y_zero] at hyt'
    rw [← hyt'] at hEpos
    exact _root_.lt_irrefl _ hEpos
  have hCE : C ∣ E := ⟨i * J * D * C, by rw [hA3]; ring⟩
  have hCCE : C * C ∣ delta b * E := ⟨delta b * (i * J * D), by rw [hA3]; ring⟩
  have ht₀t' : t₀ ∣ t' :=
    (ArithmeticPellStrongDivisibility.y_dvd_iff b t₀ t').mp (by rw [hyt₀, hyt']; exact hCE)
  have hCt' : C ∣ t' := by
    have h := ArithmeticPellIndexDivisibility.ordinate_divides_index b t₀ t' ht₀t'
      (by rw [hyt₀, hyt']; exact hCCE)
    rwa [hyt₀] at h
  have h2t₀t' : 2 * t₀ ≤ t' := le_trans h2t₀ (le_of_dvd ht'pos hCt')
  -- `ψ(t'') ≡ ψ(t₀) (mod χ(t'))`, then the doubled step-down lemma
  have hbase : (b + 2) % F = (g + 2) % F := by rw [← hGg]; exact hGF.symm
  have hxpos : 0 < xcoord t' b := lt_of_lt_of_le (by norm_num : (0 : V) < 1) (one_le_x t' b)
  have hxF : xcoord t' b ∣ F := ⟨xcoord t' b, by rw [hxt']; exact hFf⟩
  have hyF : ycoord t'' b % F = ycoord t₀ b % F := by
    calc ycoord t'' b % F = ycoord t'' g % F := (pp_base_transfer b g F hFpos hbase t'').2
      _ = H % F := by rw [hyt'']
      _ = C % F := hHC
      _ = ycoord t₀ b % F := by rw [hyt₀]
  have hyx : ycoord t'' b % xcoord t' b = ycoord t₀ b % xcoord t' b := by
    calc ycoord t'' b % xcoord t' b = (ycoord t'' b % F) % xcoord t' b :=
          (ArithmeticPellResidueClasses.mod_reduce _ _ _ hxpos hxF).symm
      _ = (ycoord t₀ b % F) % xcoord t' b := by rw [hyF]
      _ = ycoord t₀ b % xcoord t' b := ArithmeticPellResidueClasses.mod_reduce _ _ _ hxpos hxF
  have hstep := ArithmeticPellResidueClasses.doubled_step_down b t' t₀ t'' ht₀pos h2t₀t'
    (Or.inl (pp_double_x_mod b t'' t₀ (xcoord t' b) hxpos hyx))
  have hred : t'' % C = t₀ % C ∨ (t'' + t₀) % C = 0 := by
    rcases hstep with h | h
    · left
      calc t'' % C = (t'' % t') % C :=
            (ArithmeticPellResidueClasses.mod_reduce t'' C t' hCpos hCt').symm
        _ = (t₀ % t') % C := by rw [h]
        _ = t₀ % C := ArithmeticPellResidueClasses.mod_reduce t₀ C t' hCpos hCt'
    · right
      calc (t'' + t₀) % C = ((t'' + t₀) % t') % C :=
            (ArithmeticPellResidueClasses.mod_reduce _ C t' hCpos hCt').symm
        _ = 0 % C := by rw [h]
        _ = 0 := zero_mod C
  -- `t'' ≡ B (mod C)`, since `C ∣ G − 1`
  have hCg : C ∣ g + 1 := by
    refine ⟨D * m, ?_⟩
    have h : g + 1 + 1 = C * (D * m) + 1 := by
      calc g + 1 + 1 = g + 2 := by ring
        _ = G := hGg.symm
        _ = 1 + D * C * m := hGm
        _ = C * (D * m) + 1 := by ring
    exact add_right_cancel h
  have hHB : t'' % C = B % C := by
    have h1 : ycoord t'' g % C = t'' % C :=
      (ArithmeticPellCongruences.residue_mod t'' g C hCg hCpos).2
    rw [hyt''] at h1
    rw [← h1, hA6]
    exact mod_add_mul B j hCpos
  -- the final index argument (`productPell_index` externally)
  have ht₀mod : t₀ % C = t₀ := mod_eq_self_of_lt ht₀C
  rcases hred with h | h
  · have hBt : B % C = t₀ := by rw [← hHB, h, ht₀mod]
    rcases lt_or_eq_of_le hBC with hlt | heq
    · rw [mod_eq_self_of_lt hlt] at hBt
      rw [hBt]
      exact hyt₀.symm
    · exfalso
      rw [heq, mod_self] at hBt
      exact (pos_iff_ne_zero.mp ht₀pos) hBt.symm
  · have hBt0 : (B + t₀) % C = 0 := by
      have h' : (t'' + t₀) % C = (B + t₀) % C := pp_mod_add hCpos hHB rfl
      rw [← h']
      exact h
    have hsum : B + t₀ = C := by
      have hle : C ≤ B + t₀ := by
        by_contra hn
        have hlt : B + t₀ < C := not_le.mp hn
        rw [mod_eq_self_of_lt hlt] at hBt0
        have hpos : 0 < B + t₀ :=
          lt_of_lt_of_le (lt_trans (by norm_num : (0 : V) < 1) hB) (by simp : B ≤ B + t₀)
        rw [hBt0] at hpos
        exact _root_.lt_irrefl _ hpos
      obtain ⟨w, hw⟩ : ∃ w : V, B + t₀ = w + C := ⟨B + t₀ - C, (tsub_add_cancel_of_le hle).symm⟩
      have hwC : w < C := by
        have h' : w + C < C + C := by
          rw [← hw]; exact add_lt_add_of_le_of_lt hBC ht₀C
        exact lt_of_add_lt_add_right h'
      rw [hw, mod_add_remove_right hCpos, mod_eq_self_of_lt hwC] at hBt0
      rw [hw, hBt0, zero_add]
    rcases hpar with h2B | hodd
    · have h1 : B ≤ t₀ := by
        have h' : B + B ≤ B + t₀ := by rw [hsum, ← two_mul]; exact h2B
        exact le_of_add_le_add_left h'
      have h2 : t₀ ≤ B := by
        have h' : t₀ + t₀ ≤ B + t₀ := by rw [hsum, ← two_mul]; exact h2t₀
        exact le_of_add_le_add_right h'
      have hBt : B = t₀ := le_antisymm h1 h2
      rw [hBt]
      exact hyt₀.symm
    · exfalso
      obtain ⟨q2, hq2⟩ := (pp_parity b t₀).1
      have e : B + 2 * t₀ = 2 * q2 := by
        rw [← hq2, hyt₀, ← hsum]; ring
      have h1 : (B + 2 * t₀) % 2 = B % 2 := mod_add_mul' B t₀ (by norm_num : (0 : V) < 2)
      rw [e, mod_mul_self_right, hodd] at h1
      exact absurd h1 (by norm_num)

set_option maxHeartbeats 1000000 in
/-- Necessity: the witnesses, built inside `V`, with both free witnesses
positive and for every positive `J`. -/
theorem exists_ProductPellConds (b B J : V) (hB : 1 < B) (hJ : 0 < J) :
    ∃ i j D E F G H I : V, 0 < i ∧ 0 < j ∧
      ProductPellConds (b + 2) B (ycoord B b) J i j D E F G H I := by
  have hB2 : 2 ≤ B := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hB
  have hBpos : 0 < B := lt_trans (by norm_num : (0 : V) < 1) hB
  obtain ⟨C, hC⟩ : ∃ C : V, C = ycoord B b := ⟨_, rfl⟩
  rw [← hC]
  have h2BC : 2 * B ≤ C := by rw [hC]; exact pp_two_mul_le_y b B hB2
  have hBC : B < C := lt_of_lt_of_le (pp_lt_two_mul B hBpos) h2BC
  have hCpos : 0 < C := lt_trans hBpos hBC
  -- `D = χ_A(B)²`
  obtain ⟨D, hD⟩ : ∃ D : V, D = 1 + delta b * C * C := ⟨_, rfl⟩
  have hDs : D = xcoord B b * xcoord B b := by
    rw [ArithmeticPellRecurrence.norm, ← hC]; exact hD
  have hDpos : 0 < D := by
    rw [hD]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * C * C)
  -- `E = ψ_A(t')`, a positive multiple of `J D C²`
  have hN : 0 < J * D * C * C := mul_pos (mul_pos (mul_pos hJ hDpos) hCpos) hCpos
  obtain ⟨t', ht'pos, i, hi⟩ := ArithmeticPellPigeonhole.ordinate_dvd b (J * D * C * C) hN
  obtain ⟨E, hE⟩ : ∃ E : V, E = ycoord t' b := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact lt_of_lt_of_le ht'pos (time_le_y t' b)
  have hA3 : E = i * J * D * C * C := by rw [hE, hi]; ring
  have hipos : 0 < i := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0] at hA3
    rw [hA3] at hEpos
    simp only [zero_mul] at hEpos
    exact _root_.lt_irrefl _ hEpos
  -- `F = χ_A(t')²`
  obtain ⟨F, hF⟩ : ∃ F : V, F = 1 + delta b * E * E := ⟨_, rfl⟩
  have hFs : F = xcoord t' b * xcoord t' b := by
    rw [ArithmeticPellRecurrence.norm, ← hE]; exact hF
  have hFpos : 0 < F := by
    rw [hF]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * E * E)
  obtain ⟨k, hFk⟩ : ∃ k : V, F = 1 + C * k := by
    refine ⟨delta b * E * (i * J * D * C), ?_⟩
    calc F = 1 + delta b * E * E := hF
      _ = 1 + delta b * E * (i * J * D * C * C) := by rw [← hA3]
      _ = 1 + C * (delta b * E * (i * J * D * C)) := by ring
  -- `G = A + F (CD + 1 − A) = g + 2`
  have hle : b + 2 ≤ C * D + 1 :=
    le_trans (pp_base_le_CD b C D hCpos hD) (by simp : C * D ≤ C * D + 1)
  obtain ⟨w, hw⟩ : ∃ w : V, w + (b + 2) = C * D + 1 :=
    ⟨C * D + 1 - (b + 2), tsub_add_cancel_of_le hle⟩
  obtain ⟨g, hg⟩ : ∃ g : V, g = b + F * w := ⟨_, rfl⟩
  have hA5 : g + 2 + F * (b + 2) = b + 2 + F * (C * D + 1) := by
    rw [hg, ← hw]; ring
  have hCg : C ∣ g + 1 := by
    refine ⟨D + k * w, ?_⟩
    have h : g + 1 + 1 = C * (D + k * w) + 1 := by
      calc g + 1 + 1 = (w + (b + 2)) + C * k * w := by rw [hg, hFk]; ring
        _ = (C * D + 1) + C * k * w := by rw [hw]
        _ = C * (D + k * w) + 1 := by ring
    exact add_right_cancel h
  -- `H = ψ_G(B) = B + jC`
  have hHmod : ycoord B g % C = B := by
    rw [(ArithmeticPellCongruences.residue_mod B g C hCg hCpos).2]
    exact mod_eq_self_of_lt hBC
  obtain ⟨j, hj⟩ : ∃ j : V, C * j + B = ycoord B g := by
    refine ⟨ycoord B g / C, ?_⟩
    have h := div_add_mod (ycoord B g) C
    rwa [hHmod] at h
  obtain ⟨H, hH⟩ : ∃ H : V, H = ycoord B g := ⟨_, rfl⟩
  rw [← hH] at hj
  have hA6 : H = B + j * C := by rw [← hj]; ring
  have hjpos : 0 < j := by
    have h2BH : 2 * B ≤ H := by rw [hH]; exact pp_two_mul_le_y g B hB2
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0, mul_zero, zero_add] at hj
    rw [← hj] at h2BH
    exact _root_.lt_irrefl _ (lt_of_lt_of_le (pp_lt_two_mul B hBpos) h2BH)
  -- `H ≡ C (mod F)` by base transfer, since `G ≡ A (mod F)`
  have hbase : (g + 2) % F = (b + 2) % F := by
    rw [hg, show b + F * w + 2 = b + 2 + F * w by ring]
    exact mod_add_mul' (b + 2) w hFpos
  have hHF : H % F = C % F := by
    rw [hH, hC]
    exact (pp_base_transfer g b F hFpos hbase B).2
  -- `I = χ_G(B)²`
  obtain ⟨I, hI⟩ : ∃ I : V, I = 1 + delta g * H * H := ⟨_, rfl⟩
  have hIs : I = xcoord B g * xcoord B g := by
    rw [ArithmeticPellRecurrence.norm, ← hH]; exact hI
  refine ⟨i, j, D, E, F, g + 2, H, I, hipos, hjpos, ⟨?_, hHF, ?_, hA3, ?_, hA5, hA6, ?_⟩⟩
  · exact ⟨xcoord B b * xcoord t' b * xcoord B g, by rw [hDs, hFs, hIs]; ring⟩
  · rw [hD]; unfold delta; ring
  · rw [hF]; unfold delta; ring
  · rw [hI]; unfold delta; ring

/-- **Lemma 2.27 in every model of `𝗜𝚺₁`**, for the base `A = b + 2`, with an
arbitrary positive `J` and positive witnesses `i, j`. -/
theorem lemma_2_27 (b B C J : V) (hB : 1 < B) (hBC : B ≤ C)
    (hpar : 2 * B ≤ C ∨ B % 2 = 1) (hJ : 0 < J) :
    C = ycoord B b ↔ ∃ i j D E F G H I : V, 0 < i ∧ 0 < j ∧
      ProductPellConds (b + 2) B C J i j D E F G H I := by
  constructor
  · rintro rfl
    exact exists_ProductPellConds b B J hB hJ
  · rintro ⟨i, j, D, E, F, G, H, I, hi, -, h⟩
    exact psi_of_ProductPellConds b B C J i j D E F G H I hB hBC hpar hJ hi h

/-- The coprimality remark after Lemma 2.27: `F` and `J` have a unit Bézout
certificate (internal coprimality), since `J ∣ E` and `F ≡ 1 (mod E)`. -/
theorem ProductPellConds.coprime_J {b B C J i j D E F G H I : V}
    (h : ProductPellConds (b + 2) B C J i j D E F G H I) : Bez F J 1 := by
  have hF : F = 1 + delta b * E * E := pp_norm_of_literal b F E h.A4
  have hFJ : F = 1 + J * (delta b * E * (i * D * C * C)) := by
    rw [hF]
    calc 1 + delta b * E * E = 1 + delta b * E * (i * J * D * C * C) := by rw [← h.A3]
      _ = 1 + J * (delta b * E * (i * D * C * C)) := by ring
  rw [hFJ]
  exact pp_bez_symm (pp_bez_one_add J _)

end DiophantineConsistency.ModelProductPell
