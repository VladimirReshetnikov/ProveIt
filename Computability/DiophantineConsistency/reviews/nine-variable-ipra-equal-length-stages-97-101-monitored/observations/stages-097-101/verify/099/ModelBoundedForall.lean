import DiophantineConsistency.ModelBoundedForallArith
import DiophantineConsistency.ModelRepPrec

/-! # The bounded-universal CRT certificate inside models of `𝗜𝚺₁`

`dpr_iff` is the internal Davis–Putnam–Robinson bounded-quantifier theorem for
the certificate of `BoundedForallRepresentation`: for natural expressions `e f`,

  `(∃ u a c, CritV e f b x u a c) ↔ ∀ k < x b, ∃ w, e(k, w) = f(k, w)`,

where `T = (e(x b, u) + f(x b, u) + x b)!`, `B = ∏_{k < x b} ((k+1)·T+1)` and
`CritV` says `B ∣ (u_i+1)!·binom a_i (u_i+1)`, `B ∣ (c+1)·T+1`,
`e(c, a) ≡ f(c, a) (mod B)`.

* Decoding (`dpr_forward`) uses an irreducible divisor `p` of `(k+1)·T+1`
  (least divisor `> 1`, no primes), which exceeds every value bounded by the
  factorial scale; the falling-factorial divisibility puts every `a_i` within
  `u_i` of a residue modulo `p`.
* Encoding (`dpr_backward`) bounds packed row witnesses (`npair`) and then runs a
  single Σ₁ Chinese-remainder induction over the rows, extending all coordinates
  at once (`crt_rows`).

`holds_finiteRep` evaluates the certificate syntax with the leaf interfaces
`PowCase`, `BinomCase`, `FactCase`; `certificateCase_of` combines both into
`ModelRepPrec.CertificateCase`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelBoundedForall
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelDifferenceRing ModelScalarPR ModelRepBasic ModelRepArith ModelRepInterfaces
open ArithmeticPow ArithmeticBinomPascal ArithmeticBinomFactorial ArithmeticGcdNormalization
open ModelBetaFunction ModelBoundedForallArith
open BoundedForallRepresentation (CertificateVar parameter upper encoded index upperMap encodedMap)

/-! ### Packed rows and their definability -/

section Rows
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A natural expression at row `k`, with witness coordinates unpacked from `W`. -/
def rowVal {σ : Type} {m : ℕ} (g : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) (k W : V) : V :=
  g.evalSemiring (Sum.elim (Option.elim' k x) (fun i => unNpair i W))

/-- The row equation with a packed witness. -/
def RowP {σ : Type} {m : ℕ} (e f : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) (k W : V) : Prop :=
  rowVal e x k W = rowVal f x k W

/-- Coordinatewise equality of residues of two packed vectors. -/
def ResEq (m : ℕ) (A W M : V) : Prop := ∀ i : Fin m, unNpair i A % M = unNpair i W % M

instance rowVal_definable {σ : Type} {m : ℕ} (g : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) :
    𝚺₁-Function₂[V] (rowVal g x) :=
  evalSemiring_definable' g
    (fun j (z : Fin 2 → V) => Sum.elim (Option.elim' (z 0) x) (fun i => unNpair i (z 1)) j)
    (by
      intro j
      rcases j with (_ | j) | i
      · exact HierarchySymbol.DefinableFunction.var 0
      · exact HierarchySymbol.DefinableFunction.const (x j)
      · exact HierarchySymbol.DefinableFunction₁.comp (F := unNpair i)
          (HierarchySymbol.DefinableFunction.var 1))

instance rowP_definable {σ : Type} {m : ℕ} (e f : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) :
    𝚺₁-Relation[V] (RowP e f x) :=
  HierarchySymbol.Definable.comp₂ (P := Eq) (rowVal_definable e x) (rowVal_definable f x)

instance resEq_definable (m : ℕ) : 𝚺₁-Relation₃[V] (ResEq m : V → V → V → Prop) := by
  show 𝚺₁.Definable (fun v : Fin 3 → V => ∀ i : Fin m, unNpair i (v 0) % v 2 = unNpair i (v 1) % v 2)
  exact HierarchySymbol.Definable.fintype_all (fun i => by definability)

theorem rowP_npair {σ : Type} {m : ℕ} (e f : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) (k : V)
    (w : Fin m → V) :
    RowP e f x k (npair w) ↔
      e.evalSemiring (Sum.elim (Option.elim' k x) w) = f.evalSemiring (Sum.elim (Option.elim' k x) w) := by
  have hw : (fun i => unNpair i (npair w)) = w := funext fun i => unNpair_npair i w
  unfold RowP rowVal
  rw [hw]

end Rows

/-! ### The internal certificate -/

section Certificate
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {σ : Type} {m : ℕ}

/-- The factorial scale at the coordinate bounds `u`. -/
def tvalV (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V) (u : Fin m → V) : V :=
  fact (e.evalSemiring (Sum.elim (Option.elim' (x b) x) u) +
    f.evalSemiring (Sum.elim (Option.elim' (x b) x) u) + x b)

/-- The internal CRT certificate. -/
def CritV (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V) (u a : Fin m → V) (c : V) :
    Prop :=
  (∀ i : Fin m, prodM (tvalV e f b x u) (x b) ∣ fact (u i + 1) * binom (a i) (u i + 1)) ∧
    ((c + 1) * tvalV e f b x u + 1) % prodM (tvalV e f b x u) (x b) = 0 ∧
    e.evalSemiring (Sum.elim (Option.elim' c x) a) % prodM (tvalV e f b x u) (x b) =
      f.evalSemiring (Sum.elim (Option.elim' c x) a) % prodM (tvalV e f b x u) (x b)

/-- Decoding one row from a certificate. -/
theorem dpr_forward (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V) (u a : Fin m → V)
    (c : V) (h : CritV e f b x u a c) (k : V) (hk : k < x b) :
    ∃ w : Fin m → V, e.evalSemiring (Sum.elim (Option.elim' k x) w) =
      f.evalSemiring (Sum.elim (Option.elim' k x) w) := by
  obtain ⟨T, hT⟩ : ∃ T, T = tvalV e f b x u := ⟨_, rfl⟩
  obtain ⟨bnd, hbnd⟩ : ∃ bnd, bnd = e.evalSemiring (Sum.elim (Option.elim' (x b) x) u) +
      f.evalSemiring (Sum.elim (Option.elim' (x b) x) u) + x b := ⟨_, rfl⟩
  have hTb : T = fact bnd := by rw [hT, hbnd]; rfl
  have hTpos : 0 < T := by rw [hTb]; exact fact_pos _
  obtain ⟨h1, h2, h3⟩ : (∀ i : Fin m, prodM T (x b) ∣ fact (u i + 1) * binom (a i) (u i + 1)) ∧
      ((c + 1) * T + 1) % prodM T (x b) = 0 ∧
      e.evalSemiring (Sum.elim (Option.elim' c x) a) % prodM T (x b) =
        f.evalSemiring (Sum.elim (Option.elim' c x) a) % prodM T (x b) := by
    rw [hT]
    exact h
  have hM1 : 1 < (k + 1) * T + 1 := by
    have h11 : 1 ≤ (k + 1) * T := one_le_mul le_add_self (pos_iff_one_le.mp hTpos)
    exact lt_of_le_of_lt h11 (lt_add_one _)
  obtain ⟨p, hp1, hpM, hirr⟩ := exists_irred_dvd _ hM1
  have hp0 : 0 < p := lt_of_le_of_lt (Arithmetic.zero_le 1) hp1
  have hpB : p ∣ prodM T (x b) := dvd_trans hpM (dvd_prodM T (x b) k hk)
  have hnot1 : ¬ p ∣ 1 := fun h' => hp1.ne' (LO.FirstOrder.Arithmetic.dvd_one_iff.mp h')
  have hpT : ¬ p ∣ T := by
    intro hpt
    have h1' : ((k + 1) * T + 1) % p = 1 % p :=
      mod_add_remove_left_of_dvd (Dvd.dvd.mul_left hpt (k + 1)) hp0
    rw [mod_eq_zero_iff_dvd.mpr hpM] at h1'
    exact hnot1 (mod_eq_zero_iff_dvd.mp h1'.symm)
  have hpbig : bnd < p := by
    by_contra hle
    exact hpT (by rw [hTb]; exact dvd_fact_of_le bnd p (not_lt.mp hle) hp0)
  have hbez : Bez p T 1 := bez_of_irred hirr hpT
  -- the encoded index is `k` modulo `p`
  have hcB : ((c + 1) * T + 1) % p = 0 := by
    have hh := mod_eq_of_dvd_of_mod_eq (x := (c + 1) * T + 1) (y := 0)
      (by rw [h2, LO.FirstOrder.Arithmetic.zero_mod]) hpB
    rwa [LO.FirstOrder.Arithmetic.zero_mod] at hh
  have hck : c % p = k % p := by
    obtain ⟨α, β, hαβ⟩ := (bez_one_iff_ring (a := p) (b := T)).mp hbez
    obtain ⟨q1, hq1⟩ := ringSub_of_mod_eq
      (show ((c + 1) * T + 1) % p = ((k + 1) * T + 1) % p by
        rw [hcB, mod_eq_zero_iff_dvd.mpr hpM])
    apply mod_eq_of_sub_eq (q := (ι c - ι k) * α + β * q1)
    simp only [map_add, map_mul, map_one] at hq1
    linear_combination (-(ι c - ι k)) * hαβ + β * hq1
  -- every encoded coordinate is congruent to a value within its bound
  have hcoord : ∀ i : Fin m, ∃ w : V, w ≤ u i ∧ a i % p = w % p := by
    intro i
    have hpi : p ∣ fact (u i + 1) * binom (a i) (u i + 1) := dvd_trans hpB (h1 i)
    obtain ⟨j, hj, hpj⟩ := dvd_factor_of_dvd_desc p (a i) hnot1
      (fun _ _ hxy => euclid_of_irred hirr hxy) (u i + 1) hpi
    have hju : j ≤ u i := LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hj
    rcases le_total j (a i) with hja | haj
    · refine ⟨j, hju, ?_⟩
      obtain ⟨q, hq⟩ := hpj
      have hai : a i = j + p * q := by
        rw [← hq]
        exact (add_tsub_cancel_of_le hja).symm
      rw [hai, mod_add_mul' j q hp0]
    · exact ⟨a i, le_trans haj hju, rfl⟩
  choose w hwu hwmod using hcoord
  have hval : ∀ j, Sum.elim (Option.elim' c x) a j % p = Sum.elim (Option.elim' k x) w j % p := by
    intro j
    rcases j with (_ | j) | i
    · exact hck
    · rfl
    · exact hwmod i
  have hle : ∀ j, Sum.elim (Option.elim' k x) w j ≤ Sum.elim (Option.elim' (x b) x) u j := by
    intro j
    rcases j with (_ | j) | i
    · exact le_of_lt hk
    · exact le_rfl
    · exact hwu i
  refine ⟨w, ?_⟩
  have heq3 := mod_eq_of_dvd_of_mod_eq h3 hpB
  have he1 := evalSemiring_mod' e hp0 hval
  have hf1 := evalSemiring_mod' f hp0 hval
  have he2 : e.evalSemiring (Sum.elim (Option.elim' k x) w) < p :=
    lt_of_le_of_lt (le_trans (evalSemiring_mono' e hle)
      (by rw [hbnd]; exact le_trans le_self_add le_self_add)) hpbig
  have hf2 : f.evalSemiring (Sum.elim (Option.elim' k x) w) < p :=
    lt_of_le_of_lt (le_trans (evalSemiring_mono' f hle)
      (by rw [hbnd]; exact le_trans le_add_self le_self_add)) hpbig
  rw [← mod_eq_self_of_lt he2, ← mod_eq_self_of_lt hf2, ← he1, ← hf1]
  exact heq3

/-- A common bound for packed row witnesses. -/
theorem exists_row_bound (e f : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) (N : V)
    (H : ∀ k < N, ∃ W, RowP e f x k W) (n : V) :
    n ≤ N → ∃ U, ∀ k < n, ∃ W ≤ U, RowP e f x k W := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    exact ⟨0, fun k hk => absurd hk (not_lt.mpr (Arithmetic.zero_le k))⟩
  case succ n ih =>
    intro hn
    obtain ⟨U, hU⟩ := ih (le_trans le_self_add hn)
    obtain ⟨W, hW⟩ := H n (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hn)
    refine ⟨U + W, fun k hk => ?_⟩
    rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hk) with hlt | heq
    · obtain ⟨W', hW'U, hW'⟩ := hU k hlt
      exact ⟨W', le_trans hW'U le_self_add, hW'⟩
    · refine ⟨W, le_add_self, ?_⟩
      rw [heq]
      exact hW

set_option maxHeartbeats 4000000 in
/-- The Chinese-remainder induction over the rows, all coordinates at once. -/
theorem crt_rows (e f : NatExpr (Option σ ⊕ Fin m)) (x : σ → V) (N T U : V)
    (hcop : ∀ i j, i < j → j < N → Bez ((i + 1) * T + 1) ((j + 1) * T + 1) 1)
    (hU : ∀ k < N, ∃ W ≤ U, RowP e f x k W) (n : V) :
    n ≤ N → ∃ A c P : V, 0 < P ∧
      (∀ k < n, c % ((k + 1) * T + 1) = k % ((k + 1) * T + 1) ∧
        ∃ W ≤ U, RowP e f x k W ∧ ResEq m A W ((k + 1) * T + 1)) ∧
      (∀ k < n, (k + 1) * T + 1 ∣ P) ∧
      ∀ j < N, n ≤ j → ∃ u v w z : V,
        1 + P * u + ((j + 1) * T + 1) * v = P * w + ((j + 1) * T + 1) * z := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    exact ⟨0, 0, 1, _root_.zero_lt_one, fun k hk => absurd hk (not_lt.mpr (Arithmetic.zero_le k)),
      fun k hk => absurd hk (not_lt.mpr (Arithmetic.zero_le k)), fun j _ _ => ⟨0, 0, 1, 0, by ring⟩⟩
  case succ n ih =>
    intro hn1
    have hnN : n < N := LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hn1
    obtain ⟨A, c, P, hP, hrows, hdvd, hbez⟩ := ih (le_of_lt hnN)
    obtain ⟨W, hWU, hW⟩ := hU n hnN
    have hM : 0 < (n + 1) * T + 1 := beta_succ_pos _
    have hb : Bez P ((n + 1) * T + 1) 1 := hbez n hnN le_rfl
    obtain ⟨c', hc'1, qc, hqc⟩ := crt_step hP hM hb c n
    have hcoord : ∀ i : Fin m, ∃ a' : V,
        a' % ((n + 1) * T + 1) = unNpair i W % ((n + 1) * T + 1) ∧
          ∃ q : DiffRing V, ι a' - ι (unNpair i A) = ι P * q :=
      fun i => crt_step hP hM hb (unNpair i A) (unNpair i W)
    choose a' ha'1 qa ha'2 using hcoord
    refine ⟨npair a', c', P * ((n + 1) * T + 1), mul_pos hP hM, ?_, ?_, ?_⟩
    · intro k hk
      rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hk) with hlt | heq
      · obtain ⟨hck, W', hW'U, hW', hres⟩ := hrows k hlt
        refine ⟨(mod_eq_of_ringDvd hqc (hdvd k hlt)).trans hck, W', hW'U, hW', ?_⟩
        intro i
        rw [unNpair_npair]
        exact (mod_eq_of_ringDvd (ha'2 i) (hdvd k hlt)).trans (hres i)
      · rw [heq]
        refine ⟨hc'1, W, hWU, hW, ?_⟩
        intro i
        rw [unNpair_npair]
        exact ha'1 i
    · intro k hk
      rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hk) with hlt | heq
      · exact Dvd.dvd.mul_right (hdvd k hlt) _
      · rw [heq]
        exact dvd_mul_left _ _
    · intro j hj hnj
      exact bez_mul (hbez j hj (le_trans le_self_add hnj))
        (hcop n j (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hnj) hj)

/-- The certificate built from the row induction. -/
theorem crit_of_rows (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V) (U A c T : V)
    (hT : T = tvalV e f b x (fun _ => U))
    (hcop : ∀ i j, i < j → j < x b → Bez ((i + 1) * T + 1) ((j + 1) * T + 1) 1)
    (hrows : ∀ k < x b, c % ((k + 1) * T + 1) = k % ((k + 1) * T + 1) ∧
        ∃ W ≤ U, RowP e f x k W ∧ ResEq m A W ((k + 1) * T + 1)) :
    CritV e f b x (fun _ => U) (fun i => unNpair i A) c := by
  show (∀ i : Fin m, prodM (tvalV e f b x (fun _ => U)) (x b) ∣
        fact (U + 1) * binom (unNpair i A) (U + 1)) ∧
      ((c + 1) * tvalV e f b x (fun _ => U) + 1) % prodM (tvalV e f b x (fun _ => U)) (x b) = 0 ∧
      e.evalSemiring (Sum.elim (Option.elim' c x) (fun i => unNpair i A)) %
          prodM (tvalV e f b x (fun _ => U)) (x b) =
        f.evalSemiring (Sum.elim (Option.elim' c x) (fun i => unNpair i A)) %
          prodM (tvalV e f b x (fun _ => U)) (x b)
  rw [← hT]
  have hMpos : ∀ k : V, 0 < (k + 1) * T + 1 := fun k => beta_succ_pos _
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have key := (mod_prodM T (x b) (fact (U + 1) * binom (unNpair i A) (U + 1)) 0 hcop
      (fun k hk => by
        obtain ⟨_, W, hWU, _, hres⟩ := hrows k hk
        have hw : unNpair i W ≤ U := le_trans (unNpair_le' i W) hWU
        have hdiv := dvd_desc_of_dvd _ (unNpair i A) (unNpair i W)
          (dvd_tsub_of_mod_eq (hres i)) (U + 1) (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mpr hw)
        rw [LO.FirstOrder.Arithmetic.zero_mod]
        exact mod_eq_zero_iff_dvd.mpr hdiv) (x b) le_rfl).1
    rw [LO.FirstOrder.Arithmetic.zero_mod] at key
    exact mod_eq_zero_iff_dvd.mp key
  · have key := (mod_prodM T (x b) ((c + 1) * T + 1) 0 hcop
      (fun k hk => by
        obtain ⟨hck, _⟩ := hrows k hk
        rw [lin_mod_congr T hck, LO.FirstOrder.Arithmetic.mod_self, LO.FirstOrder.Arithmetic.zero_mod]) (x b) le_rfl).1
    rwa [LO.FirstOrder.Arithmetic.zero_mod] at key
  · exact (mod_prodM T (x b) _ _ hcop
      (fun k hk => by
        obtain ⟨hck, W, _, hW, hres⟩ := hrows k hk
        have hval : ∀ j : Option σ ⊕ Fin m,
            Sum.elim (Option.elim' c x) (fun i : Fin m => unNpair i A) j % ((k + 1) * T + 1) =
            Sum.elim (Option.elim' k x) (fun i : Fin m => unNpair i W) j % ((k + 1) * T + 1) := by
          intro j
          rcases j with (_ | j) | i
          · exact hck
          · rfl
          · exact hres i
        have he := evalSemiring_mod' e (hMpos k) hval
        have hf := evalSemiring_mod' f (hMpos k) hval
        have hW' : rowVal e x k W = rowVal f x k W := hW
        unfold rowVal at hW'
        rw [he, hf, hW']) (x b) le_rfl).1

/-- Encoding all rows into a certificate. -/
theorem dpr_backward (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V)
    (H : ∀ k < x b, ∃ w : Fin m → V, e.evalSemiring (Sum.elim (Option.elim' k x) w) =
      f.evalSemiring (Sum.elim (Option.elim' k x) w)) :
    ∃ u a : Fin m → V, ∃ c : V, CritV e f b x u a c := by
  have H' : ∀ k < x b, ∃ W, RowP e f x k W := by
    intro k hk
    obtain ⟨w, hw⟩ := H k hk
    exact ⟨npair w, (rowP_npair e f x k w).mpr hw⟩
  obtain ⟨U, hU⟩ := exists_row_bound e f x (x b) H' (x b) le_rfl
  obtain ⟨T, hT⟩ : ∃ T, T = tvalV e f b x (fun _ => U) := ⟨_, rfl⟩
  obtain ⟨bnd, hbnd⟩ : ∃ bnd, bnd =
      e.evalSemiring (Sum.elim (Option.elim' (x b) x) (fun _ : Fin m => U)) +
        f.evalSemiring (Sum.elim (Option.elim' (x b) x) (fun _ : Fin m => U)) + x b := ⟨_, rfl⟩
  have hTb : T = fact bnd := by rw [hT, hbnd]; rfl
  have hxb : x b ≤ bnd := by rw [hbnd]; exact le_add_self
  have hdivT : ∀ d ≤ bnd, 0 < d → d ∣ T := by
    rw [hTb]
    exact dvd_fact_of_le bnd
  have hcop : ∀ i j, i < j → j < x b → Bez ((i + 1) * T + 1) ((j + 1) * T + 1) 1 :=
    fun i j hij hj => moduli_bez T bnd i j hdivT hij (le_trans (le_of_lt hj) hxb)
  obtain ⟨A, c, P, _, hrows, _, _⟩ := crt_rows e f x (x b) T U hcop hU (x b) le_rfl
  exact ⟨fun _ => U, fun i => unNpair i A, c, crit_of_rows e f b x U A c T hT hcop hrows⟩

/-- The internal Davis–Putnam–Robinson bounded-quantifier theorem. -/
theorem dpr_iff (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V) :
    (∃ u a : Fin m → V, ∃ c : V, CritV e f b x u a c) ↔
      ∀ k < x b, ∃ w : Fin m → V, e.evalSemiring (Sum.elim (Option.elim' k x) w) =
        f.evalSemiring (Sum.elim (Option.elim' k x) w) := by
  constructor
  · rintro ⟨u, a, c, h⟩ k hk
    exact dpr_forward e f b x u a c h k hk
  · exact dpr_backward e f b x

end Certificate

/-! ### The certificate syntax -/

section Syntax
variable {σ : Type} {m : ℕ}

/-- The same syntax and type as the private `BoundedForallRepresentation.dvdGraphs`. -/
def dvdGraphsRep {τ : Type*} {f g : (τ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) :
    Rep τ (fun v => f v ∣ g v) :=
  (Rep.compose (ArithmeticRep.dvd (0 : Fin 2) 1) (twoArgs r s)).ofIff (fun _ => Iff.rfl)

def nRep (b : σ) : GraphRep (fun v : CertificateVar σ m → ℕ => v (parameter b)) :=
  GraphRep.coordinate (parameter b)

def tRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :=
  (((e.graphRep.reindex (upperMap b)).add (f.graphRep.reindex (upperMap b))).add
    (nRep (m := m) b)).factorial

def bRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :=
  BoundedForallRepresentation.productGraph (nRep (m := m) b) (tRep e f b)

def coordRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (i : Fin m) :=
  dvdGraphsRep (bRep e f b)
    ((((GraphRep.coordinate (upper i : CertificateVar σ m)).add (GraphRep.constant 1)).factorial).mul
      ((GraphRep.coordinate (encoded i : CertificateVar σ m)).binomial
        ((GraphRep.coordinate (upper i : CertificateVar σ m)).add (GraphRep.constant 1))))

def indexRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :=
  PowerRepresentation.modEqGraphs
    ((((GraphRep.coordinate (index : CertificateVar σ m)).add (GraphRep.constant 1)).mul
      (tRep e f b)).add (GraphRep.constant 1))
    (GraphRep.constant 0) (bRep e f b)

def evalRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :=
  PowerRepresentation.modEqGraphs (e.graphRep.reindex encodedMap)
    (f.graphRep.reindex encodedMap) (bRep e f b)

section Raw
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The scale computed by the syntax, before simplification. -/
def tRaw (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (v : CertificateVar σ m → V) : V :=
  fact (e.evalSemiring (fun i => v (upperMap b i)) + f.evalSemiring (fun i => v (upperMap b i)) +
    v (parameter b))

/-- The encoded product computed by the syntax, before simplification. -/
def encProdRaw (N T : V) : V :=
  (power T N * (fact N * binom (power ((N + ((1 : ℕ) : V)) * T + ((1 : ℕ) : V)) N +
      ((2 : ℕ) : V) + N) N)) %
    (T * (power ((N + ((1 : ℕ) : V)) * T + ((1 : ℕ) : V)) N + ((2 : ℕ) : V)) - ((1 : ℕ) : V))

/-- The internal meaning of `finiteRep`, before simplification. -/
def FinCritRaw (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (v : CertificateVar σ m → V) : Prop :=
  (∀ i : Fin m, encProdRaw (v (parameter b)) (tRaw e f b v) ∣
      fact (v (upper i) + ((1 : ℕ) : V)) * binom (v (encoded i)) (v (upper i) + ((1 : ℕ) : V))) ∧
    ((v index + ((1 : ℕ) : V)) * tRaw e f b v + ((1 : ℕ) : V)) %
        encProdRaw (v (parameter b)) (tRaw e f b v) =
      ((0 : ℕ) : V) % encProdRaw (v (parameter b)) (tRaw e f b v) ∧
    e.evalSemiring (fun i => v (encodedMap i)) % encProdRaw (v (parameter b)) (tRaw e f b v) =
      f.evalSemiring (fun i => v (encodedMap i)) % encProdRaw (v (parameter b)) (tRaw e f b v)

theorem encProdRaw_eq (N T : V) (hT : 0 < T) : encProdRaw N T = prodM T N := by
  unfold encProdRaw
  simp only [Nat.cast_one, Nat.cast_ofNat]
  exact encProd_eq N T hT

end Raw

theorem graphHolds_tRep (hf : FactCase) (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    GraphHolds (tRep e f b) (fun V _ _ v => tRaw e f b v) :=
  graphHolds_factorial hf (graphHolds_add (graphHolds_add
    (graphHolds_reindex (graphHolds_natExpr e) (upperMap b))
    (graphHolds_reindex (graphHolds_natExpr f) (upperMap b)))
    (graphHolds_coordinate (parameter b : CertificateVar σ m)))

theorem graphHolds_bRep (hp : PowCase) (hb : BinomCase) (hf : FactCase)
    (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    GraphHolds (bRep e f b) (fun V _ _ v => encProdRaw (v (parameter b)) (tRaw e f b v)) := by
  have hN := graphHolds_coordinate (parameter b : CertificateVar σ m)
  have hT := graphHolds_tRep hf e f b
  have hQ := graphHolds_add (graphHolds_pow hp (graphHolds_add (graphHolds_mul
    (graphHolds_add hN (graphHolds_constant 1)) hT) (graphHolds_constant 1)) hN)
    (graphHolds_constant 2)
  exact graphHolds_mod
    (graphHolds_mul (graphHolds_pow hp hT hN)
      (graphHolds_mul (graphHolds_factorial hf hN) (graphHolds_binomial hb (graphHolds_add hQ hN) hN)))
    (graphHolds_sub (graphHolds_mul hT hQ) (graphHolds_constant 1))

theorem holds_coordRep (hp : PowCase) (hb : BinomCase) (hf : FactCase)
    (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (i : Fin m) :
    Holds (coordRep e f b i) (fun V _ _ v => encProdRaw (v (parameter b)) (tRaw e f b v) ∣
      fact (v (upper i) + ((1 : ℕ) : V)) * binom (v (encoded i)) (v (upper i) + ((1 : ℕ) : V))) := by
  have hu := graphHolds_add (graphHolds_coordinate (upper i : CertificateVar σ m))
    (graphHolds_constant 1)
  exact holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_dvdGraphs (graphHolds_bRep hp hb hf e f b)
      (graphHolds_mul (graphHolds_factorial hf hu)
        (graphHolds_binomial hb (graphHolds_coordinate (encoded i : CertificateVar σ m)) hu)))

theorem holds_finiteRep (hp : PowCase) (hb : BinomCase) (hf : FactCase)
    (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    Holds (BoundedForallRepresentation.finiteRep e f b) (fun V _ _ v => FinCritRaw e f b v) := by
  have hT := graphHolds_tRep hf e f b
  have hB := graphHolds_bRep hp hb hf e f b
  have hI := graphHolds_add (graphHolds_mul (graphHolds_add
    (graphHolds_coordinate (index : CertificateVar σ m)) (graphHolds_constant 1)) hT)
    (graphHolds_constant 1)
  have hidx : Holds (indexRep e f b) _ := holds_modEqGraphs hI (graphHolds_constant 0) hB
  have hev : Holds (evalRep e f b) _ :=
    holds_modEqGraphs (graphHolds_reindex (graphHolds_natExpr e) encodedMap)
      (graphHolds_reindex (graphHolds_natExpr f) encodedMap) hB
  have hall := holds_allFin m
    (fun (i : Fin m) (v : CertificateVar σ m → ℕ) =>
      MRDP.encodedModuliProduct (v (parameter b)) (BoundedForallRepresentation.scale e f b v) ∣
        (v (upper i) + 1).factorial * (v (encoded i)).choose (v (upper i) + 1))
    (coordRep e f b) _ (fun i => holds_coordRep hp hb hf e f b i)
  exact holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_conjunction hall (holds_conjunction hidx hev))

/-- The certificate's raw internal meaning is the clean certificate `CritV`. -/
theorem finCritRaw_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → V) (u a : Fin m → V) (c : Fin 1 → V) :
    FinCritRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c) ↔ CritV e f b x u a (c 0) := by
  have hup : (fun i => Sum.elim (Sum.elim (Sum.elim x u) a) c (upperMap b i)) =
      Sum.elim (Option.elim' (x b) x) u := by
    funext j
    rcases j with (_ | j) | i <;> rfl
  have hen : (fun i => Sum.elim (Sum.elim (Sum.elim x u) a) c (encodedMap i)) =
      Sum.elim (Option.elim' (c 0) x) a := by
    funext j
    rcases j with (_ | j) | i <;> rfl
  have htv : tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c) = tvalV e f b x u := by
    unfold tRaw tvalV
    rw [hup]
    rfl
  have hB : encProdRaw (x b) (tvalV e f b x u) = prodM (tvalV e f b x u) (x b) :=
    encProdRaw_eq _ _ (fact_pos _)
  show ((∀ i : Fin m, encProdRaw (x b) (tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c)) ∣
        fact (u i + ((1 : ℕ) : V)) * binom (a i) (u i + ((1 : ℕ) : V))) ∧
      ((c 0 + ((1 : ℕ) : V)) * tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c) +
          ((1 : ℕ) : V)) % encProdRaw (x b) (tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c)) =
        ((0 : ℕ) : V) % encProdRaw (x b) (tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c)) ∧
      e.evalSemiring (fun i => Sum.elim (Sum.elim (Sum.elim x u) a) c (encodedMap i)) %
          encProdRaw (x b) (tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c)) =
        f.evalSemiring (fun i => Sum.elim (Sum.elim (Sum.elim x u) a) c (encodedMap i)) %
          encProdRaw (x b) (tRaw e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c))) ↔ _
  rw [htv, hen, hB]
  simp only [Nat.cast_one, Nat.cast_zero, LO.FirstOrder.Arithmetic.zero_mod]
  exact Iff.rfl

/-- `ModelRepPrec.CertificateCase` from the three arithmetic leaves. -/
theorem certificateCase_of (hp : PowCase) (hb : BinomCase) (hf : FactCase) :
    ModelRepPrec.CertificateCase := by
  intro σ m e f b
  refine holds_congr _ ?_ (holds_existsBlock (holds_existsBlock (holds_existsBlock
    (holds_finiteRep hp hb hf e f b))))
  intro V _ _ x
  refine Iff.trans ?_ (dpr_iff e f b x)
  constructor
  · rintro ⟨u, a, c, h⟩
    exact ⟨u, a, c 0, (finCritRaw_iff e f b x u a c).mp h⟩
  · rintro ⟨u, a, c, h⟩
    exact ⟨u, a, fun _ => c, (finCritRaw_iff e f b x u a (fun _ => c)).mpr h⟩

end Syntax

end DiophantineConsistency.ModelBoundedForall
