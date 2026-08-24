import GowersSzemeredi.Sections06_07
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole

/-!
# Freiman restrictions from small graph difference sets

This file proves Lemma 7.5.  The paper's displayed Plünnecke--Ruzsa estimate
for `4k Γ - 4k Γ` has an exponent that is too small.  The proof below avoids
that doubled sumset: it bounds the vertical fiber of `k Γ - k Γ` by injecting
its product with `Γ` into `2k Γ - 2k Γ`, where exponent `4k` is valid.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor75_mem_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (p : ZMod N × ZMod N) :
    p ∈ functionGraph B phi ↔ p.1 ∈ B ∧ p.2 = phi p.1 := by
  classical
  simp [functionGraph, Prod.ext_iff, eq_comm]

private lemma cor75_card_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (functionGraph B phi).card = B.card := by
  classical
  unfold functionGraph
  rw [Finset.card_image_iff.mpr]
  intro x _ y _ h
  exact congrArg Prod.fst h

private lemma cor75_sub_mem_nsmul_sub_nsmul {G : Type*}
    [DecidableEq G] [AddCommGroup G] (A : Finset G) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) {m : Nat} (hm : 0 < m) :
    a - b ∈ m • A - m • A := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hpad : n • b ∈ n • A := Finset.nsmul_mem_nsmul hb
  have hpos : n • b + a ∈ n • A + A := Finset.add_mem_add hpad ha
  have hneg : n • b + b ∈ n • A + A := Finset.add_mem_add hpad hb
  rw [Nat.succ_eq_add_one, add_nsmul, one_nsmul]
  convert Finset.sub_mem_sub hpos hneg using 1
  abel

private lemma cor75_sub_mem_double_nsmul {G : Type*}
    [DecidableEq G] [AddCommGroup G] (A : Finset G) {p q : G} {m : Nat}
    (hp : p ∈ m • A - m • A) (hq : q ∈ m • A - m • A) :
    p - q ∈ (m + m) • A - (m + m) • A := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hp
  obtain ⟨u', hu', v', hv', rfl⟩ := Finset.mem_sub.mp hq
  have hpos : u + v' ∈ m • A + m • A := Finset.add_mem_add hu hv'
  have hneg : v + u' ∈ m • A + m • A := Finset.add_mem_add hv hu'
  rw [add_nsmul]
  convert Finset.sub_mem_sub hpos hneg using 1
  abel

private lemma cor75_multiset_sum_mem_nsmul {G : Type*}
    [DecidableEq G] [AddCommMonoid G] (A : Finset G) (s : Multiset G)
    (hs : ∀ x ∈ s, x ∈ A) : s.sum ∈ s.card • A := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : a ∈ A := hs a (by simp)
      have hs' : ∀ x ∈ s, x ∈ A := by
        intro x hx
        exact hs x (by simp [hx])
      have hi := ih hs'
      rw [Multiset.sum_cons, Multiset.card_cons, add_nsmul, one_nsmul]
      convert Finset.add_mem_add hi ha using 1
      exact add_comm _ _

private lemma cor75_multiset_graph_sum {G H : Type*}
    [AddCommMonoid G] [AddCommMonoid H] (phi : G → H) (s : Multiset G) :
    (s.map fun x => (x, phi x)).sum = (s.sum, (s.map phi).sum) := by
  induction s using Multiset.induction_on with
  | empty =>
      apply Prod.ext <;> simp
  | cons x s ih => simp [ih]

private lemma cor75_natCast_injective {N a b : Nat} [NeZero N]
    (ha : a < N) (hb : b < N) (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

private def cor75Coeff (N T : Nat) (q : Bool × Fin T) : ZMod N :=
  if q.1 then -((q.2.val + 1 : Nat) : ZMod N)
  else ((q.2.val + 1 : Nat) : ZMod N)

private lemma cor75_coeff_ne_zero {N T : Nat} [NeZero N]
    (hTN : T < N) (q : Bool × Fin T) : cor75Coeff N T q ≠ 0 := by
  rcases q with ⟨b, i⟩
  have hnpos : 0 < i.val + 1 := by omega
  have hnN : i.val + 1 < N := by omega
  have hcast : ((i.val + 1 : Nat) : ZMod N) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => (not_lt_of_ge (Nat.le_of_dvd hnpos hdvd)) hnN
  cases b with
  | false =>
      change ((i.val + 1 : Nat) : ZMod N) ≠ 0
      exact hcast
  | true =>
      change -((i.val + 1 : Nat) : ZMod N) ≠ 0
      exact neg_ne_zero.mpr hcast

private lemma cor75_verticalFiber_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (C : Real)
    (hB : B.Nonempty) (hk : 0 < k) (_hC : 0 < C)
    (hsmall : (((functionGraph B phi - functionGraph B phi).card : Real) ≤
      C * (functionGraph B phi).card)) :
    let Gamma := functionGraph B phi
    let S := k • Gamma - k • Gamma
    let K := (Finset.univ : Finset (ZMod N)).filter fun y => (0, y) ∈ S
    (K.card : Real) ≤ C ^ (4 * k) := by
  classical
  dsimp only
  let Gamma := functionGraph B phi
  let S := k • Gamma - k • Gamma
  let T := (2 * k) • Gamma - (2 * k) • Gamma
  let K := (Finset.univ : Finset (ZMod N)).filter fun y => (0, y) ∈ S
  have hGammaCard : Gamma.card = B.card := cor75_card_functionGraph B phi
  have hGamma : Gamma.Nonempty := by
    obtain ⟨b, hb⟩ := hB
    refine ⟨(b, phi b), ?_⟩
    exact (cor75_mem_functionGraph B phi _).2 ⟨hb, rfl⟩
  have hGammaPosR : (0 : Real) < Gamma.card := by exact_mod_cast hGamma.card_pos
  have hPR := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub
    hGamma Gamma (2 * k) (2 * k)
  have hPRR : (T.card : Real) ≤
      ((((Gamma - Gamma).card : Real) / Gamma.card) ^ (4 * k)) * Gamma.card := by
    dsimp only [T]
    have hcast : (((((2 * k) • Gamma - (2 * k) • Gamma).card : NNRat) : Real)) ≤
        (((((Gamma - Gamma).card : NNRat) / Gamma.card) ^
          ((2 * k) + (2 * k))) * Gamma.card : NNRat) := by
      exact_mod_cast hPR
    norm_num at hcast ⊢
    simpa only [show 2 * k + 2 * k = 4 * k by omega] using hcast
  have hratio : (((Gamma - Gamma).card : Real) / Gamma.card) ≤ C := by
    apply (div_le_iff₀ hGammaPosR).2
    simpa [Gamma] using hsmall
  have hratio0 : 0 ≤ (((Gamma - Gamma).card : Real) / Gamma.card) := by positivity
  have hTbound : (T.card : Real) ≤ C ^ (4 * k) * Gamma.card := by
    calc
      (T.card : Real) ≤
          (((Gamma - Gamma).card : Real) / Gamma.card) ^ (4 * k) * Gamma.card := hPRR
      _ ≤ C ^ (4 * k) * Gamma.card := by
        gcongr
  obtain ⟨b0, hb0⟩ := hB
  let gamma0 : ZMod N × ZMod N := (b0, phi b0)
  let F : ZMod N × ZMod N → ZMod N × ZMod N := fun p =>
    ((p.2, phi p.2) - gamma0) - (0, p.1)
  have hMaps : Set.MapsTo F (↑(K ×ˢ B)) (↑T) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    have hGraphP : (p.2, phi p.2) ∈ Gamma := by
      exact (cor75_mem_functionGraph B phi _).2 ⟨hp.2, rfl⟩
    have hGraph0 : gamma0 ∈ Gamma := by
      exact (cor75_mem_functionGraph B phi _).2 ⟨hb0, rfl⟩
    have hz : (p.2, phi p.2) - gamma0 ∈ S := by
      exact cor75_sub_mem_nsmul_sub_nsmul Gamma hGraphP hGraph0 hk
    have hy : (0, p.1) ∈ S := by
      simpa [K] using hp.1
    have hd := cor75_sub_mem_double_nsmul Gamma hz hy
    change F p ∈ T
    simpa only [F, T, show k + k = 2 * k by omega] using hd
  have hInj : Set.InjOn F (↑(K ×ˢ B)) := by
    intro p hp q hq heq
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    have hfirst := congrArg (fun z : ZMod N × ZMod N => z.1) heq
    have hpq : p.2 = q.2 := by
      dsimp only [F, gamma0] at hfirst
      simp only [Prod.fst_sub, sub_zero] at hfirst
      exact sub_left_injective hfirst
    have hsecond := congrArg (fun z : ZMod N × ZMod N => z.2) heq
    dsimp only [F, gamma0] at hsecond
    simp only [Prod.snd_sub] at hsecond
    rw [hpq] at hsecond
    have : p.1 = q.1 := sub_right_injective hsecond
    exact Prod.ext this hpq
  have hcardInj : (K ×ˢ B).card ≤ T.card :=
    Finset.card_le_card_of_injOn F hMaps hInj
  have hcardInjR : (K.card : Real) * B.card ≤ T.card := by
    exact_mod_cast (by simpa using hcardInj)
  rw [hGammaCard] at hTbound
  have hBPosR : (0 : Real) < B.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨b0, hb0⟩)
  nlinarith

private lemma cor75_exists_good_d {N k L : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) (hk : 0 < k) (hK : K.Nonempty)
    (hsize : 4 * k * K.card * L ≤ N) :
    ∃ d : ZMod N, d ≠ 0 ∧
      ∀ q : Bool × Fin (k * L), cor75Coeff N (k * L) q * d ∉ K := by
  classical
  have hprime := Fact.out (p := Nat.Prime N)
  have hN2 : 2 ≤ N := hprime.two_le
  have hTLT : k * L < N := by
    have hKpos : 0 < K.card := hK.card_pos
    by_cases hL : L = 0
    · simp [hL]
      exact NeZero.pos N
    · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
      nlinarith
  by_contra hgood
  have hall : ∀ d : ZMod N, d ≠ 0 →
      ∃ q : Bool × Fin (k * L), cor75Coeff N (k * L) q * d ∈ K := by
    intro d hd
    by_contra hnone
    apply hgood
    refine ⟨d, hd, ?_⟩
    intro q hq
    exact hnone ⟨q, hq⟩
  let D0 := {d : ZMod N // d ∈ (Finset.univ.erase 0 : Finset (ZMod N))}
  let Q := Bool × Fin (k * L)
  have hd0ne (d : D0) : (d : ZMod N) ≠ 0 := by
    exact Finset.ne_of_mem_erase d.property
  choose q hq using fun d : D0 => hall d (hd0ne d)
  let target := Q × {w : ZMod N // w ∈ K}
  let F : D0 → target := fun d =>
    (q d, ⟨cor75Coeff N (k * L) (q d) * (d : ZMod N), hq d⟩)
  have hFInj : Function.Injective F := by
    intro d e hde
    have hqeq : q d = q e := congrArg Prod.fst hde
    have hweq := congrArg (fun z : target => (z.2 : ZMod N)) hde
    dsimp only [F] at hweq
    rw [hqeq] at hweq
    have hc := cor75_coeff_ne_zero hTLT (q e)
    exact Subtype.ext (mul_left_cancel₀ hc hweq)
  have hcards := Fintype.card_le_of_injective F hFInj
  have hD0card : Fintype.card D0 = N - 1 := by
    dsimp only [D0]
    rw [Fintype.card_coe]
    simp [ZMod.card]
  have htargetCard : Fintype.card target = 2 * (k * L) * K.card := by
    dsimp only [target, Q]
    simp [Fintype.card_prod, Fintype.card_coe]
  rw [hD0card, htargetCard] at hcards
  have hhalf : 2 * (2 * (k * L) * K.card) ≤ N := by
    nlinarith
  by_cases hL : L = 0
  · simp [hL] at hcards
    omega
  · have hq2 : 2 ≤ 2 * (k * L) * K.card := by
      have hKpos := hK.card_pos
      have hLpos := Nat.pos_of_ne_zero hL
      have : 0 < (k * L) * K.card := Nat.mul_pos (Nat.mul_pos hk hLpos) hKpos
      simpa only [one_mul, Nat.mul_assoc] using Nat.mul_le_mul_left 2 this
    omega

private lemma cor75_coeff_rep_pos {N k L n : Nat} [NeZero N]
    (hn0 : 0 < n) (hn : n ≤ k * L) :
    ∃ q : Bool × Fin (k * L), cor75Coeff N (k * L) q = (n : ZMod N) := by
  refine ⟨(false, ⟨n - 1, by omega⟩), ?_⟩
  simp [cor75Coeff, Nat.sub_add_cancel (by omega : 1 ≤ n)]

private lemma cor75_coeff_rep_neg {N k L n : Nat} [NeZero N]
    (hn0 : 0 < n) (hn : n ≤ k * L) :
    ∃ q : Bool × Fin (k * L), cor75Coeff N (k * L) q = -(n : ZMod N) := by
  refine ⟨(true, ⟨n - 1, by omega⟩), ?_⟩
  simp [cor75Coeff, Nat.sub_add_cancel (by omega : 1 ≤ n)]

/-- Gowers's Lemma 7.5, with the proof's erroneous doubled sumset repaired. -/
theorem lemma_7_5_holds : lemma_7_5 := by
  intro N k _ B phi C hprime hk hC hsmall
  letI : Fact N.Prime := ⟨hprime⟩
  classical
  by_cases hB : B.Nonempty
  swap
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hB]
    · simp [FreimanHom]
  let Gamma := functionGraph B phi
  let S := k • Gamma - k • Gamma
  let K := (Finset.univ : Finset (ZMod N)).filter fun y => (0, y) ∈ S
  have hKbound : (K.card : Real) ≤ C ^ (4 * k) := by
    simpa only [Gamma, S, K] using
      cor75_verticalFiber_bound B phi C hB hk hC hsmall
  have hGamma : Gamma.Nonempty := by
    obtain ⟨b, hb⟩ := hB
    refine ⟨(b, phi b), ?_⟩
    exact (cor75_mem_functionGraph B phi _).2 ⟨hb, rfl⟩
  have hK : K.Nonempty := by
    obtain ⟨g, hg⟩ := hGamma
    have hzero : ((0 : ZMod N), (0 : ZMod N)) ∈ S := by
      have := cor75_sub_mem_nsmul_sub_nsmul Gamma hg hg hk
      change (0 : ZMod N × ZMod N) ∈ S
      simpa only [S, sub_self] using this
    refine ⟨0, ?_⟩
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzero
  have hKposR : (0 : Real) < K.card := by exact_mod_cast hK.card_pos
  have hDpos : 0 < C ^ (4 * k) := pow_pos hC _
  let L := N / (4 * k * K.card)
  have hdenomPos : 0 < 4 * k * K.card := by positivity
  have hsize : 4 * k * K.card * L ≤ N := by
    simpa [L, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self N (4 * k * K.card)
  obtain ⟨d, hd, havoid⟩ := cor75_exists_good_d K hk hK hsize
  let domain : Finset (ZMod N × Nat) := B ×ˢ Finset.range (L + 1)
  let color : ZMod N × Nat → ZMod N := fun z => phi z.1 - (z.2 : ZMod N) * d
  let average : Real := (B.card : Real) * (L + 1) / N
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have havgHyp : ((Finset.univ : Finset (ZMod N)).card : Nat) • average ≤
      ∑ z ∈ domain, (1 : Real) := by
    simp [average, domain, ZMod.card]
    field_simp [ne_of_gt hNpos]
    norm_num
  obtain ⟨a, _ha, ha⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s := domain) (t := (Finset.univ : Finset (ZMod N)))
    (f := color) (w := fun _ => (1 : Real)) (b := average)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty havgHyp
  let fiber := domain.filter fun z => color z = a
  have haFiber : average ≤ (fiber.card : Real) := by
    simpa [fiber] using ha
  let B' := fiber.image Prod.fst
  have hFiberInj : Set.InjOn (fun z : ZMod N × Nat => z.1) (↑fiber) := by
    intro z hz w hw hfirst
    have hzmem : z ∈ domain ∧ color z = a := by simpa [fiber] using hz
    have hwmem : w ∈ domain ∧ color w = a := by simpa [fiber] using hw
    have hLltN : L + 1 ≤ N := by
      have hdenom4 : 4 ≤ 4 * k * K.card := by
        have hk1 : 1 ≤ k := by omega
        have hK1 : 1 ≤ K.card := hK.card_pos
        calc
          4 = 4 * 1 * 1 := by norm_num
          _ ≤ 4 * k * K.card := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hk1) hK1
      have : L < N := by
        dsimp only [L]
        exact Nat.div_lt_self (NeZero.pos N) (by omega)
      omega
    have hmul : (z.2 : ZMod N) * d = (w.2 : ZMod N) * d := by
      have heq : phi z.1 - (z.2 : ZMod N) * d =
          phi w.1 - (w.2 : ZMod N) * d := by
        dsimp only [color] at hzmem hwmem
        exact hzmem.2.trans hwmem.2.symm
      change z.1 = w.1 at hfirst
      rw [hfirst] at heq
      exact sub_right_injective heq
    have hcast : (z.2 : ZMod N) = (w.2 : ZMod N) := mul_right_cancel₀ hd hmul
    have hzlt : z.2 < N := by
      have := (Finset.mem_product.mp hzmem.1).2
      simp only [Finset.mem_range] at this
      omega
    have hwlt : w.2 < N := by
      have := (Finset.mem_product.mp hwmem.1).2
      simp only [Finset.mem_range] at this
      omega
    exact Prod.ext hfirst (cor75_natCast_injective hzlt hwlt hcast)
  have hB'card : B'.card = fiber.card := by
    exact Finset.card_image_iff.mpr hFiberInj
  have hB'sub : B' ⊆ B := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdom : z ∈ domain := (Finset.mem_filter.mp hz).1
    exact (Finset.mem_product.mp hzdom).1
  have hfloor : N < (L + 1) * (4 * k * K.card) := by
    exact (Nat.div_lt_iff_lt_mul hdenomPos).mp (by simp [L])
  have hscale : (N : Real) ≤ (L + 1) * (8 * (k : Real) * C ^ (4 * k)) := by
    have hfloorR : (N : Real) < (L + 1) * (4 * k * K.card) := by exact_mod_cast hfloor
    have hLK : (0 : Real) ≤ L + 1 := by positivity
    nlinarith
  have hsizeB : (B.card : Real) / (8 * (k : Real) * C ^ (4 * k)) ≤ B'.card := by
    rw [hB'card]
    apply le_trans ?_ haFiber
    dsimp only [average]
    have hdenR : 0 < 8 * (k : Real) * C ^ (4 * k) := by positivity
    apply (div_le_div_iff₀ hdenR hNpos).2
    have hmul := mul_le_mul_of_nonneg_left hscale
      (show (0 : Real) ≤ B.card by positivity)
    nlinarith
  have hB'mem (x : ZMod N) (hx : x ∈ B') :
      ∃ j : Nat, j ≤ L ∧ phi x = a + (j : ZMod N) * d := by
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    have hz' := Finset.mem_filter.mp hz
    have hzrange := (Finset.mem_product.mp hz'.1).2
    refine ⟨z.2, by simpa using hzrange, ?_⟩
    dsimp only [color] at hz'
    rw [← hzx]
    exact (sub_eq_iff_eq_add).mp hz'.2
  let idx : ZMod N → Nat := fun x => if hx : x ∈ B' then
    Classical.choose (hB'mem x hx) else 0
  have hidxLe (x : ZMod N) (hx : x ∈ B') : idx x ≤ L := by
    dsimp only [idx]
    rw [dif_pos hx]
    exact (Classical.choose_spec (hB'mem x hx)).1
  have hphiIdx (x : ZMod N) (hx : x ∈ B') :
      phi x = a + (idx x : ZMod N) * d := by
    dsimp only [idx]
    rw [dif_pos hx]
    exact (Classical.choose_spec (hB'mem x hx)).2
  have hFreiman : FreimanHom k B' phi := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
    intro s t hsB' htB' hscard htcard hsum
    have hsB : ∀ ⦃x⦄, x ∈ s → x ∈ B := fun x hx => hB'sub (hsB' hx)
    have htB : ∀ ⦃x⦄, x ∈ t → x ∈ B := fun x hx => hB'sub (htB' hx)
    have hsGraph : (s.map fun x => (x, phi x)).sum ∈ k • Gamma := by
      have hm := cor75_multiset_sum_mem_nsmul Gamma
        (s.map fun x => (x, phi x)) (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
          exact (cor75_mem_functionGraph B phi _).2 ⟨hsB hx, rfl⟩)
      simpa [hscard] using hm
    have htGraph : (t.map fun x => (x, phi x)).sum ∈ k • Gamma := by
      have hm := cor75_multiset_sum_mem_nsmul Gamma
        (t.map fun x => (x, phi x)) (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
          exact (cor75_mem_functionGraph B phi _).2 ⟨htB hx, rfl⟩)
      simpa [htcard] using hm
    let ys : Nat := (s.map idx).sum
    let yt : Nat := (t.map idx).sum
    have hys : ys ≤ k * L := by
      dsimp only [ys]
      have hm := Multiset.sum_le_card_nsmul (s.map idx) L (by
        intro j hj
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hj
        exact hidxLe x (hsB' hx))
      simpa [Multiset.card_map, hscard] using hm
    have hyt : yt ≤ k * L := by
      dsimp only [yt]
      have hm := Multiset.sum_le_card_nsmul (t.map idx) L (by
        intro j hj
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hj
        exact hidxLe x (htB' hx))
      simpa [Multiset.card_map, htcard] using hm
    have hcastS : (s.map fun x => (idx x : ZMod N)).sum = (ys : ZMod N) := by
      dsimp only [ys]
      induction s using Multiset.induction_on <;> simp_all
    have hcastT : (t.map fun x => (idx x : ZMod N)).sum = (yt : ZMod N) := by
      dsimp only [yt]
      induction t using Multiset.induction_on <;> simp_all
    have hsPhi : (s.map phi).sum = k • a + (ys : ZMod N) * d := by
      calc
        (s.map phi).sum =
            (s.map fun x => a + (idx x : ZMod N) * d).sum := by
          congr 1
          exact Multiset.map_congr rfl fun x hx => hphiIdx x (hsB' hx)
        _ = (s.map fun _ => a).sum +
            (s.map fun x => (idx x : ZMod N) * d).sum := Multiset.sum_map_add
        _ = k • a + (ys : ZMod N) * d := by
          rw [Multiset.sum_map_mul_right]
          simpa [hscard] using congrArg (fun z : ZMod N => k • a + z * d) hcastS
    have htPhi : (t.map phi).sum = k • a + (yt : ZMod N) * d := by
      calc
        (t.map phi).sum =
            (t.map fun x => a + (idx x : ZMod N) * d).sum := by
          congr 1
          exact Multiset.map_congr rfl fun x hx => hphiIdx x (htB' hx)
        _ = (t.map fun _ => a).sum +
            (t.map fun x => (idx x : ZMod N) * d).sum := Multiset.sum_map_add
        _ = k • a + (yt : ZMod N) * d := by
          rw [Multiset.sum_map_mul_right]
          simpa [htcard] using congrArg (fun z : ZMod N => k • a + z * d) hcastT
    by_contra hPhi
    let y : ZMod N := (s.map phi).sum - (t.map phi).sum
    have hy0 : y ≠ 0 := sub_ne_zero.mpr hPhi
    have hyPair : (0, y) ∈ S := by
      have hm := Finset.sub_mem_sub hsGraph htGraph
      rw [cor75_multiset_graph_sum phi s, cor75_multiset_graph_sum phi t] at hm
      simpa [S, y, hsum] using hm
    have hyK : y ∈ K := by
      simpa [K] using hyPair
    dsimp only [y] at hy0 hyK
    rw [hsPhi, htPhi] at hy0 hyK
    have hysyt : ys ≠ yt := by
      intro heq
      rw [heq] at hy0
      simp at hy0
    by_cases hst : yt ≤ ys
    · let n := ys - yt
      have hn0 : 0 < n := by
        dsimp only [n]
        omega
      have hn : n ≤ k * L := by omega
      obtain ⟨q, hq⟩ := cor75_coeff_rep_pos (N := N) hn0 hn
      have hbad := havoid q
      apply hbad
      rw [hq]
      convert hyK using 1
      dsimp only [n]
      rw [Nat.cast_sub hst]
      ring
    · have hts : ys ≤ yt := by omega
      let n := yt - ys
      have hn0 : 0 < n := by
        dsimp only [n]
        omega
      have hn : n ≤ k * L := by omega
      obtain ⟨q, hq⟩ := cor75_coeff_rep_neg (N := N) hn0 hn
      have hbad := havoid q
      apply hbad
      rw [hq]
      convert hyK using 1
      dsimp only [n]
      rw [Nat.cast_sub hts]
      ring
  exact ⟨B', hB'sub, hsizeB, hFreiman⟩

end LeanProofs.GowersSzemeredi
