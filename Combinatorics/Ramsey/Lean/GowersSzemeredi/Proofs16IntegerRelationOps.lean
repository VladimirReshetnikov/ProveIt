import GowersSzemeredi.Proofs16IntegerCoordinateOps

/-! Scaling and finite pointwise sums of integer-covered relations.
The original product of graph counts and width exponents is retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IntegerMultiplyLinearWith.relationSum {N k : Nat} [NeZero N]
    {Q1 E1 Q2 E2 : Real → Real} {Gamma1 Gamma2 : Finset (Point N k × ZMod N)}
    (h1 : IntegerMultiplyLinearWith Q1 E1 Gamma1) (h2 : IntegerMultiplyLinearWith Q2 E2 Gamma2)
    {lam : Real} (hl : 0 < lam) (hl1 : lam < 1)
    (hQ2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Q2 s)
    (hE2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E2 s) :
    IntegerMultiplyLinearWith (fun s => Q1 (lam * s) * Q2 ((1 - lam) * s))
      (fun s => E1 (lam * s) * E2 ((1 - lam) * s)) (relationSum Gamma1 Gamma2) := by
  classical
  intro s hs hs1 P hP
  have ha : 0 < lam * s := mul_pos hl hs
  have ha1 : lam * s ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hl1.le hs.le]
  have hb : 0 < (1 - lam) * s := mul_pos (by linarith) hs
  have hb1 : (1 - lam) * s ≤ 1 := by nlinarith [mul_pos hl hs]
  obtain ⟨M1, q1, H1, B, nu, hH1sub, hH1mass, hBpart, hBproper, hq1, hBwidth, hnu, hcov1⟩ :=
    h1 (lam * s) ha ha1 P hP
  obtain ⟨q2, G, L, R, mu, hq2, hGsub, hGmass, hRpart, hRproper, hRwidth, hmu, hcov2⟩ :=
    h2.on_partition ((1 - lam) * s) hb hb1 (hQ2 _ hb hb1) P B hBpart (fun j => (hBproper j).toGenuine)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, q1 * q2, H1 ∩ G, boxFlatten L R,
    fun j => sumMultilinearFamily (nu (e.symm j).1) (mu (e.symm j).1 (e.symm j).2),
    ?_, ?_, boxFlatten_partition P B L R hBpart hRpart, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.inter_subset_left.trans hH1sub
  · have hsub : H1 ∪ G ⊆ P.carrier := Finset.union_subset hH1sub hGsub
    have hcu : ((H1 ∪ G).card : Real) ≤ P.carrier.card := by
      exact_mod_cast Finset.card_le_card hsub
    have hui : ((H1 ∪ G).card : Real) + (H1 ∩ G).card = H1.card + G.card := by
      exact_mod_cast Finset.card_union_add_card_inter H1 G
    have key : (1 - s) * (P.carrier.card : Real) =
        (1 - lam * s) * P.carrier.card + (1 - (1 - lam) * s) * P.carrier.card -
          P.carrier.card := by ring
    rw [key]
    linarith
  · intro j
    exact hRproper (e.symm j).1 (e.symm j).2
  · show ((q1 * q2 : Nat) : Real) ≤ Q1 (lam * s) * Q2 ((1 - lam) * s)
    push_cast
    exact mul_le_mul hq1 hq2 (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hq1)
  · intro j
    show (P.width : Real) ^ (E1 (lam * s) * E2 ((1 - lam) * s)) ≤
      ((R (e.symm j).1 (e.symm j).2).width : Real)
    rw [Real.rpow_mul (Nat.cast_nonneg _)]
    exact (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hBwidth _)
      (hE2 _ hb hb1)).trans (hRwidth _ _)
  · intro j i
    exact sumMultilinearFamily_isMultilinear _ _ (hnu _) (hmu _ _) i
  · intro j x hx hxH y hxy
    have hxR : x ∈ (R (e.symm j).1 (e.symm j).2).carrier := hx
    have hxB : x ∈ (B (e.symm j).1).carrier := IsPartition.cell_subset (hRpart _) _ hxR
    obtain ⟨y1, y2, hy1, hy2, rfl⟩ := mem_relationSum hxy
    obtain ⟨a, ha⟩ := hcov1 _ x hxB (Finset.mem_inter.mp hxH).1 y1 hy1
    obtain ⟨b, hb⟩ := hcov2 _ _ x hxR (Finset.mem_inter.mp hxH).2 y2 hy2
    refine ⟨finProdFinEquiv (a, b), ?_⟩
    show y1 + y2 = sumMultilinearFamily (nu (e.symm j).1) (mu (e.symm j).1 (e.symm j).2)
      (finProdFinEquiv (a, b)) x
    rw [sumMultilinearFamily_pair, ← ha, ← hb]

theorem IntegerMultiplyLinearWith.relationScale {N k : Nat} [NeZero N] {Q E : Real → Real}
    {Gamma : Finset (Point N k × ZMod N)} (h : IntegerMultiplyLinearWith Q E Gamma) (c : ZMod N) :
    IntegerMultiplyLinearWith Q E (relationScale c Gamma) := by
  classical
  intro s hs hs1 P hP
  obtain ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h s hs hs1 P hP
  refine ⟨M, q, H, R, fun j i x => c * mu j i x, hH, hmass, hpart, hproper, hq, hwidth,
    fun j i => (hmu j i).const_mul c, ?_⟩
  intro j x hx hxH y hxy
  obtain ⟨⟨x', y'⟩, hz, heq⟩ := Finset.mem_image.mp hxy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  obtain ⟨i, hi⟩ := hcover j x' hx hxH y' hz
  exact ⟨i, by rw [hi]⟩

theorem IntegerMultiplyLinearWith.relSumFin {N k : Nat} [NeZero N] :
    ∀ (n : Nat) {Gamma : Fin (n + 1) → Finset (Point N k × ZMod N)}
      {Q E : Fin (n + 1) → Real → Real},
      (∀ i, IntegerMultiplyLinearWith (Q i) (E i) (Gamma i)) →
      (∀ i s, 0 < s → s ≤ 1 → 0 ≤ Q i s) → (∀ i s, 0 < s → s ≤ 1 → 0 ≤ E i s) →
      IntegerMultiplyLinearWith (fun s => ∏ i, Q i (s / ((n : Real) + 1)))
        (fun s => ∏ i, E i (s / ((n : Real) + 1))) (relSumFin n Gamma)
  | 0, Gamma, Q, E, h, _, _ => by
    have hfun : ∀ (F : Fin (0 + 1) → Real → Real),
        (fun s => ∏ i, F i (s / (((0 : Nat) : Real) + 1))) = F 0 := by
      intro F; funext s; simp
    rw [hfun Q, hfun E]
    exact h 0
  | n + 1, Gamma, Q, E, h, hQ, hE => by
    have ih := IntegerMultiplyLinearWith.relSumFin n (Gamma := fun i => Gamma i.castSucc)
      (Q := fun i => Q i.castSucc) (E := fun i => E i.castSucc) (fun i => h i.castSucc)
      (fun i => hQ i.castSucc) (fun i => hE i.castSucc)
    have hn1 : (0 : Real) < (n : Real) + 1 := by positivity
    have hn2 : (0 : Real) < ((n + 1 : Nat) : Real) + 1 := by positivity
    set lam : Real := ((n : Real) + 1) / (((n + 1 : Nat) : Real) + 1) with hlam
    have hl : 0 < lam := div_pos hn1 hn2
    have hl1 : lam < 1 := by
      rw [hlam, div_lt_one hn2]; push_cast; linarith
    have hsum := IntegerMultiplyLinearWith.relationSum ih (h (Fin.last (n + 1))) hl hl1
      (hQ (Fin.last (n + 1))) (hE (Fin.last (n + 1)))
    have hA : ∀ s : Real, lam * s / ((n : Real) + 1) = s / (((n + 1 : Nat) : Real) + 1) := by
      intro s; rw [hlam]; field_simp
    have hB : ∀ s : Real, (1 - lam) * s = s / (((n + 1 : Nat) : Real) + 1) := by
      intro s; rw [hlam]; field_simp; push_cast; ring
    have hfun : ∀ F : Fin (n + 1 + 1) → Real → Real,
        (fun s => (∏ i : Fin (n + 1), F i.castSucc (lam * s / ((n : Real) + 1))) *
            F (Fin.last (n + 1)) ((1 - lam) * s)) =
          fun s => ∏ i, F i (s / (((n + 1 : Nat) : Real) + 1)) := by
      intro F; funext s
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [hA, hB]
    rw [← hfun Q, ← hfun E]
    exact hsum

end LeanProofs.GowersSzemeredi
