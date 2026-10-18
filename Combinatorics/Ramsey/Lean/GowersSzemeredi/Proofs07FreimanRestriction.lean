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

lemma cor75_mem_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (p : ZMod N × ZMod N) :
    p ∈ functionGraph B phi ↔ p.1 ∈ B ∧ p.2 = phi p.1 := by
  simp [functionGraph, Prod.ext_iff, eq_comm]

lemma cor75_card_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (functionGraph B phi).card = B.card := by
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
  intro Gamma S K
  obtain ⟨b0, hb0⟩ := hB
  have hg (b : ZMod N) (hb : b ∈ B) : (b, phi b) ∈ Gamma :=
    (cor75_mem_functionGraph B phi _).2 ⟨hb, rfl⟩
  have hGB : (Gamma.card : Real) = B.card := by exact_mod_cast cor75_card_functionGraph B phi
  have hB0 : (0 : Real) < B.card := by exact_mod_cast Finset.card_pos.mpr ⟨b0, hb0⟩
  -- `(y, b) ↦ (b, phi b) - (b0, phi b0) - (0, y)` injects `K ×ˢ B` into `2k Γ - 2k Γ`
  have hinj : K.card * B.card ≤ ((2 * k) • Gamma - (2 * k) • Gamma).card := by
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun p => (p.2, phi p.2) - (b0, phi b0) - (0, p.1))
      (fun p hp => ?_) fun p _ q _ h => ?_
    · rw [Finset.mem_coe, Finset.mem_product] at hp
      simpa only [two_mul, Finset.mem_coe] using cor75_sub_mem_double_nsmul Gamma
        (cor75_sub_mem_nsmul_sub_nsmul Gamma (hg _ hp.2) (hg b0 hb0) hk)
        (Finset.mem_filter.mp hp.1).2
    · simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, sub_zero, sub_left_inj] at h ⊢
      obtain ⟨h1, h2⟩ := h
      rw [h1, sub_right_inj] at h2
      exact ⟨h2, h1⟩
  -- Plünnecke-Ruzsa bounds `2k Γ - 2k Γ`
  have hPR := NNRat.cast_mono (K := Real)
    (Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub ⟨_, hg b0 hb0⟩ Gamma (2 * k) (2 * k))
  push_cast [hGB] at hPR
  have hratio : ((Gamma - Gamma).card : Real) / B.card ≤ C := by
    rw [div_le_iff₀ hB0, ← hGB]
    exact hsmall
  refine le_of_mul_le_mul_right ?_ hB0
  calc (K.card : Real) * B.card ≤ ((2 * k) • Gamma - (2 * k) • Gamma).card := by
        exact_mod_cast hinj
    _ ≤ (((Gamma - Gamma).card : Real) / B.card) ^ (2 * k + 2 * k) * B.card := hPR
    _ ≤ C ^ (4 * k) * B.card := by
        rw [show 2 * k + 2 * k = 4 * k by ring]
        gcongr

private lemma cor75_exists_good_d {N k L : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) (hk : 0 < k) (hK : K.Nonempty)
    (hsize : 4 * k * K.card * L ≤ N) :
    ∃ d : ZMod N, d ≠ 0 ∧
      ∀ q : Bool × Fin (k * L), cor75Coeff N (k * L) q * d ∉ K := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact ⟨1, one_ne_zero, fun q => absurd q.2.isLt (by simp)⟩
  have hkL : 0 < k * L := Nat.mul_pos hk hL
  have hTLT : k * L < N := by nlinarith [hK.card_pos]
  haveI : NeZero (k * L) := ⟨hkL.ne'⟩
  -- otherwise each `d ≠ 0` has a coefficient `q d` with `c (q d) * d ∈ K`, and
  -- `d ↦ (q d, c (q d) * d)` injects the `N - 1` nonzero residues into `Q ×ˢ K`
  by_contra! hgood
  choose! q hq using hgood
  have hinj := Finset.card_le_card_of_injOn (s := Finset.univ.erase (0 : ZMod N))
    (t := Finset.univ ×ˢ K) (fun d => (q d, cor75Coeff N (k * L) (q d) * d))
    (fun d hd => Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨Finset.mem_univ _, hq d (Finset.ne_of_mem_erase hd)⟩))
    fun d _ e _ h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      rw [h1] at h2
      exact mul_left_cancel₀ (cor75_coeff_ne_zero hTLT (q e)) h2
  have hcard : N - 1 ≤ 2 * (k * L) * K.card := by simpa [ZMod.card] using hinj
  have h4 : 2 * (2 * (k * L) * K.card) ≤ N := by linarith
  have h2 : 2 ≤ 2 * (k * L) * K.card := by nlinarith [hK.card_pos]
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
  rcases B.eq_empty_or_nonempty with rfl | ⟨b0, hb0⟩
  · exact ⟨∅, Finset.empty_subset _, by simp, by simp [FreimanHom]⟩
  let Gamma := functionGraph B phi
  let S := k • Gamma - k • Gamma
  let K := (Finset.univ : Finset (ZMod N)).filter fun y => (0, y) ∈ S
  have hKbound : (K.card : Real) ≤ C ^ (4 * k) :=
    cor75_verticalFiber_bound B phi C ⟨b0, hb0⟩ hk hC hsmall
  have hg0 : (b0, phi b0) ∈ Gamma := (cor75_mem_functionGraph B phi _).2 ⟨hb0, rfl⟩
  have h00 := cor75_sub_mem_nsmul_sub_nsmul Gamma hg0 hg0 hk
  rw [sub_self] at h00
  have hK : K.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h00⟩⟩
  -- a step `d` whose multiples `c * d` with `0 < |c| ≤ k * L` all avoid `K`
  let L := N / (4 * k * K.card)
  have hdenomPos : 0 < 4 * k * K.card := by positivity
  obtain ⟨d, hd, havoid⟩ := cor75_exists_good_d (L := L) K hk hK (Nat.mul_div_le N _)
  -- pigeonhole: a fiber of `(x, j) ↦ phi x - j * d` on `B ×ˢ [0, L]` is large
  have hD : (0 : Real) < 8 * k * C ^ (4 * k) := by positivity
  have hscale : (N : Real) ≤ (L + 1) * (8 * k * C ^ (4 * k)) := by
    have hfloor : (N : Real) < (L + 1) * (4 * k * K.card) := by
      exact_mod_cast (Nat.div_lt_iff_lt_mul hdenomPos).mp (Nat.lt_add_one L)
    linarith [mul_le_mul_of_nonneg_left hKbound (by positivity : (0 : Real) ≤ (L + 1) * (4 * k)),
      (by positivity : (0 : Real) ≤ (L + 1) * (4 * k) * C ^ (4 * k))]
  obtain ⟨a, -, ha⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := B ×ˢ Finset.range (L + 1)) (f := fun z => phi z.1 - (z.2 : ZMod N) * d)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty
    (b := (B.card : Real) / (8 * k * C ^ (4 * k))) (by
      rw [Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ hD,
        Finset.card_product, Finset.card_range]
      push_cast
      linarith [mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (α := Real) B.card)])
  let fiber := (B ×ˢ Finset.range (L + 1)).filter fun z => phi z.1 - (z.2 : ZMod N) * d = a
  let B' := fiber.image Prod.fst
  have hLN : L + 1 ≤ N := Nat.div_lt_self (NeZero.pos N) (by nlinarith [hK.card_pos])
  have hB'card : B'.card = fiber.card := Finset.card_image_of_injOn <| by
    rintro ⟨x, i⟩ hz ⟨y, j⟩ hw (rfl : x = y)
    simp only [fiber, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hz hw
    exact Prod.ext rfl (cor75_natCast_injective (hz.1.2.trans_le hLN) (hw.1.2.trans_le hLN)
      (mul_right_cancel₀ hd (sub_right_injective (hz.2.trans hw.2.symm))))
  have hB'sub : B' ⊆ B := Finset.image_subset_iff.mpr fun z hz =>
    (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  have hB'mem (x : ZMod N) (hx : x ∈ B') :
      ∃ j : Nat, j ≤ L ∧ phi x = a + (j : ZMod N) * d := by
    obtain ⟨⟨y, j⟩, hz, rfl⟩ := Finset.mem_image.mp hx
    simp only [fiber, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hz
    exact ⟨j, Nat.le_of_lt_succ hz.1.2, sub_eq_iff_eq_add.mp hz.2⟩
  choose! idx hidxLe hphiIdx using hB'mem
  refine ⟨B', hB'sub, by rw [hB'card]; exact ha, fun _ _ => Set.mem_univ _,
    fun s t hsB' htB' hscard htcard hsum => ?_⟩
  -- the graph sum, the index sum and the phase sum of one side
  have hside {u : Multiset (ZMod N)} (huB' : ∀ ⦃x⦄, x ∈ u → x ∈ (B' : Set (ZMod N)))
      (hucard : Multiset.card u = k) :
      (u.map fun x => (x, phi x)).sum ∈ k • Gamma ∧ (u.map idx).sum ≤ k * L ∧
        (u.map phi).sum = k • a + ((u.map idx).sum : ZMod N) * d := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [hucard] using cor75_multiset_sum_mem_nsmul Gamma (u.map fun x => (x, phi x))
        (Multiset.forall_mem_map_iff.mpr fun x hx =>
          (cor75_mem_functionGraph B phi _).2 ⟨hB'sub (huB' hx), rfl⟩)
    · simpa [hucard] using Multiset.sum_le_card_nsmul (u.map idx) L
        (Multiset.forall_mem_map_iff.mpr fun x hx => hidxLe x (huB' hx))
    · rw [Multiset.map_congr rfl fun x hx => hphiIdx x (huB' hx), Multiset.sum_map_add,
        Multiset.sum_map_mul_right]
      simp [hucard]
  obtain ⟨hsG, hys, hsPhi⟩ := hside hsB' hscard
  obtain ⟨htG, hyt, htPhi⟩ := hside htB' htcard
  -- the phase sums differ by a multiple `c * d ∈ K` with `|c| ≤ k * L`, which forces `c = 0`
  have hyK : (s.map phi).sum - (t.map phi).sum ∈ K := by
    simpa [K, S, hsum, cor75_multiset_graph_sum] using Finset.sub_mem_sub hsG htG
  rw [hsPhi, htPhi] at hyK ⊢
  obtain h | h | h := lt_trichotomy (s.map idx).sum (t.map idx).sum
  · obtain ⟨q, hq⟩ := cor75_coeff_rep_neg (N := N) (k := k) (L := L) (Nat.sub_pos_of_lt h)
      (by omega)
    exact (havoid q (by rw [hq]; convert hyK using 1; rw [Nat.cast_sub h.le]; ring)).elim
  · rw [h]
  · obtain ⟨q, hq⟩ := cor75_coeff_rep_pos (N := N) (k := k) (L := L) (Nat.sub_pos_of_lt h)
      (by omega)
    exact (havoid q (by rw [hq]; convert hyK using 1; rw [Nat.cast_sub h.le]; ring)).elim

end LeanProofs.GowersSzemeredi
