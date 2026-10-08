import GowersSzemeredi.Proofs16WithLemma6
import GowersSzemeredi.Proofs05BoxTransport

/-! Finite unions of relations with arbitrary multiple-multilinearity controls.

`BaseCase.properMultiplyLinear_finsetUnion` unites relations that satisfy
`MultiplyLinear` with the source's control functions. This module does the
same for `MultiplyLinearWith` and arbitrary controls.

The covers are applied one after another:

* the first relation is covered at loss `lam*s`;
* every cell of that cover is covered for the second relation at loss
  `(1-lam)*s`, with one graph count and one good set (`on_partition`);
* the two graph families are concatenated on every final cell.

Counts add and width exponents multiply. For `m+1` relations with common
controls `(Q,E)`, splitting the loss evenly gives count `(m+1)*Q(s/(m+1))`
and exponent `E(s/(m+1))^(m+1)`. The exponent is exponential in the number
of pieces. That is the price of a sequential refinement (research notes,
Section16 Part H.2), and the reason a stacked slice provider cannot be
obtained this way. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Control functions may be replaced by functions that agree on `(0,1]`. -/
theorem MultiplyLinearWith.congr_controls {N k : Nat} [NeZero N]
    {Q E Q' E' : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Q E Gamma)
    (hQ : ∀ s, 0 < s → s ≤ 1 → Q s = Q' s)
    (hE : ∀ s, 0 < s → s ≤ 1 → E s = E' s) :
    MultiplyLinearWith Q' E' Gamma := by
  intro s hs hs1 P hP
  obtain ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h s hs hs1 P hP
  refine ⟨M, q, H, R, mu, hH, hmass, hpart, hproper,
    hq.trans (hQ s hs hs1).le, ?_, hmu, hcover⟩
  intro j
  rw [← hE s hs hs1]
  exact hwidth j

/-- Multiple multilinearity passes to subrelations with the same controls. -/
theorem MultiplyLinearWith.subset {N k : Nat} [NeZero N]
    {Q E : Real → Real} {Gamma Delta : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Q E Gamma) (hsub : Delta ⊆ Gamma) :
    MultiplyLinearWith Q E Delta := by
  intro s hs hs1 P hP
  obtain ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h s hs hs1 P hP
  exact ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu,
    fun j x hx hxH y hxy => hcover j x hx hxH y (hsub hxy)⟩

/-- Concatenate two families of maps: the first `p` indices give `nu`, the
remaining `q` give `mu`. -/
def appendMultilinearFamily {N k p q : Nat} (nu : Fin p → Point N k → ZMod N)
    (mu : Fin q → Point N k → ZMod N) (i : Fin (p + q)) : Point N k → ZMod N :=
  if h : (i : Nat) < p then nu ⟨i, h⟩
  else mu ⟨i - p, by have := i.isLt; omega⟩

theorem appendMultilinearFamily_isMultilinear {N k p q : Nat}
    (nu : Fin p → Point N k → ZMod N) (mu : Fin q → Point N k → ZMod N)
    (hnu : ∀ i, IsMultilinear (nu i)) (hmu : ∀ i, IsMultilinear (mu i))
    (i : Fin (p + q)) : IsMultilinear (appendMultilinearFamily nu mu i) := by
  unfold appendMultilinearFamily
  split_ifs
  · exact hnu _
  · exact hmu _

theorem appendMultilinearFamily_left {N k p q : Nat}
    (nu : Fin p → Point N k → ZMod N) (mu : Fin q → Point N k → ZMod N)
    (i : Fin p) : appendMultilinearFamily nu mu (Fin.castAdd q i) = nu i := by
  have h : ((Fin.castAdd q i : Fin (p + q)) : Nat) < p := by
    rw [Fin.coe_castAdd]; exact i.isLt
  unfold appendMultilinearFamily
  rw [dif_pos h]
  exact congrArg nu (Fin.ext (Fin.coe_castAdd q i))

theorem appendMultilinearFamily_right {N k p q : Nat}
    (nu : Fin p → Point N k → ZMod N) (mu : Fin q → Point N k → ZMod N)
    (i : Fin q) : appendMultilinearFamily nu mu (Fin.natAdd p i) = mu i := by
  have h : ¬ ((Fin.natAdd p i : Fin (p + q)) : Nat) < p := by
    rw [Fin.coe_natAdd]; omega
  unfold appendMultilinearFamily
  rw [dif_neg h]
  exact congrArg mu (Fin.ext (show ((Fin.natAdd p i : Fin (p + q)) : Nat) - p = i by
    rw [Fin.coe_natAdd]; omega))

/-- **Union of two relations.** Cover the first relation at loss `lam*s`,
then every resulting cell for the second at loss `(1-lam)*s`. Graph counts
add and width exponents multiply. -/
theorem MultiplyLinearWith.union {N k : Nat} [NeZero N]
    {Q1 E1 Q2 E2 : Real → Real} {Gamma1 Gamma2 : Finset (Point N k × ZMod N)}
    (h1 : MultiplyLinearWith Q1 E1 Gamma1) (h2 : MultiplyLinearWith Q2 E2 Gamma2)
    {lam : Real} (hl : 0 < lam) (hl1 : lam < 1)
    (hQ2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Q2 s)
    (hE2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E2 s) :
    MultiplyLinearWith (fun s => Q1 (lam * s) + Q2 ((1 - lam) * s))
      (fun s => E1 (lam * s) * E2 ((1 - lam) * s)) (Gamma1 ∪ Gamma2) := by
  classical
  intro s hs hs1 P hP
  have ha : 0 < lam * s := mul_pos hl hs
  have ha1 : lam * s ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hl1.le hs.le]
  have hb : 0 < (1 - lam) * s := mul_pos (by linarith) hs
  have hb1 : (1 - lam) * s ≤ 1 := by nlinarith [mul_pos hl hs]
  obtain ⟨M1, q1, H1, B, nu, hH1sub, hH1mass, hBpart, hBproper, hq1, hBwidth, hnu, hcov1⟩ :=
    h1 (lam * s) ha ha1 P hP
  obtain ⟨q2, G, L, R, mu, hq2, hGsub, hGmass, hRpart, hRproper, hRwidth, hmu, hcov2⟩ :=
    h2.on_partition ((1 - lam) * s) hb hb1 (hQ2 _ hb hb1) P B hBpart hBproper
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, q1 + q2, H1 ∩ G, boxFlatten L R,
    fun j => appendMultilinearFamily (nu (e.symm j).1) (mu (e.symm j).1 (e.symm j).2),
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
  · show ((q1 + q2 : Nat) : Real) ≤ Q1 (lam * s) + Q2 ((1 - lam) * s)
    push_cast
    exact add_le_add hq1 hq2
  · intro j
    show (P.width : Real) ^ (E1 (lam * s) * E2 ((1 - lam) * s)) ≤
      ((R (e.symm j).1 (e.symm j).2).width : Real)
    rw [Real.rpow_mul (Nat.cast_nonneg _)]
    exact (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hBwidth _)
      (hE2 _ hb hb1)).trans (hRwidth _ _)
  · intro j i
    exact appendMultilinearFamily_isMultilinear _ _ (hnu _) (hmu _ _) i
  · intro j x hx hxH y hxy
    have hxR : x ∈ (R (e.symm j).1 (e.symm j).2).carrier := hx
    have hxB : x ∈ (B (e.symm j).1).carrier := IsPartition.cell_subset (hRpart _) _ hxR
    rcases Finset.mem_union.mp hxy with h | h
    · obtain ⟨i, hi⟩ := hcov1 _ x hxB (Finset.mem_inter.mp hxH).1 y h
      exact ⟨Fin.castAdd q2 i, by simp only [appendMultilinearFamily_left]; exact hi⟩
    · obtain ⟨i, hi⟩ := hcov2 _ _ x hxR (Finset.mem_inter.mp hxH).2 y h
      exact ⟨Fin.natAdd q1 i, by simp only [appendMultilinearFamily_right]; exact hi⟩

/-- **Finite unions with common controls.** `m+1` relations, each with
controls `(Q,E)`, unite with count `(m+1)*Q(s/(m+1))` and exponent
`E(s/(m+1))^(m+1)`. -/
theorem MultiplyLinearWith.fin_union {N k : Nat} [NeZero N] {Q E : Real → Real}
    (hQ : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Q s) (hE : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E s)
    (m : Nat) :
    ∀ Gamma : Fin (m + 1) → Finset (Point N k × ZMod N),
      (∀ i, MultiplyLinearWith Q E (Gamma i)) →
      MultiplyLinearWith (fun s => ((m : Real) + 1) * Q (s / ((m : Real) + 1)))
        (fun s => E (s / ((m : Real) + 1)) ^ (m + 1)) (section16FinsetUnion Gamma) := by
  induction m with
  | zero =>
    intro Gamma hGamma
    have h0 : section16FinsetUnion Gamma = Gamma 0 := by
      ext z
      simp [section16FinsetUnion, Fin.exists_fin_one]
    rw [h0]
    refine (hGamma 0).congr_controls ?_ ?_
    · intro s _ _
      simp
    · intro s _ _
      simp
  | succ m ih =>
    intro Gamma hGamma
    have hsplit : section16FinsetUnion Gamma =
        Gamma 0 ∪ section16FinsetUnion (fun i : Fin (m + 1) => Gamma i.succ) := by
      ext z
      simp [section16FinsetUnion, Fin.exists_fin_succ]
    have htail := ih (fun i => Gamma i.succ) (fun i => hGamma i.succ)
    have hpos : (0 : Real) < (m : Real) + 1 := by positivity
    have hm0 : (0 : Real) ≤ m := Nat.cast_nonneg m
    have harg : ∀ s : Real, 0 < s → s ≤ 1 →
        0 < s / ((m : Real) + 1) ∧ s / ((m : Real) + 1) ≤ 1 := by
      intro s hs hs1
      refine ⟨div_pos hs hpos, ?_⟩
      rw [div_le_one hpos]
      linarith
    have hQt : ∀ s, 0 < s → s ≤ 1 →
        0 ≤ ((m : Real) + 1) * Q (s / ((m : Real) + 1)) := by
      intro s hs hs1
      exact mul_nonneg hpos.le (hQ _ (harg s hs hs1).1 (harg s hs hs1).2)
    have hEt : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E (s / ((m : Real) + 1)) ^ (m + 1) := by
      intro s hs hs1
      exact pow_nonneg (hE _ (harg s hs hs1).1 (harg s hs hs1).2) _
    have hlam : (0 : Real) < 1 / ((m : Real) + 2) := by positivity
    have hlam1 : 1 / ((m : Real) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hu := (hGamma 0).union htail hlam hlam1 hQt hEt
    rw [hsplit]
    have hm2 : (m : Real) + 2 ≠ 0 := by positivity
    have hm1 : (m : Real) + 1 ≠ 0 := by positivity
    have hc : ((m + 1 : Nat) : Real) + 1 = (m : Real) + 2 := by push_cast; ring
    have h1 : ∀ s : Real, 1 / ((m : Real) + 2) * s = s / (((m + 1 : Nat) : Real) + 1) := by
      intro s
      rw [hc]
      ring
    have h2 : ∀ s : Real, (1 - 1 / ((m : Real) + 2)) * s / ((m : Real) + 1) =
        s / (((m + 1 : Nat) : Real) + 1) := by
      intro s
      rw [hc]
      first | (field_simp; ring) | field_simp
    refine hu.congr_controls ?_ ?_
    · intro s _ _
      show Q (1 / ((m : Real) + 2) * s) +
          ((m : Real) + 1) * Q ((1 - 1 / ((m : Real) + 2)) * s / ((m : Real) + 1)) =
        (((m + 1 : Nat) : Real) + 1) * Q (s / (((m + 1 : Nat) : Real) + 1))
      rw [h1, h2, hc]
      ring
    · intro s _ _
      show E (1 / ((m : Real) + 2) * s) *
          E ((1 - 1 / ((m : Real) + 2)) * s / ((m : Real) + 1)) ^ (m + 1) =
        E (s / (((m + 1 : Nat) : Real) + 1)) ^ (m + 1 + 1)
      rw [h1, h2]
      ring

/-- Finite unions indexed by `Fin q` with `q > 0`. -/
theorem MultiplyLinearWith.finsetUnion {N k q : Nat} [NeZero N] {Q E : Real → Real}
    (hq : 0 < q) (hQ : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Q s)
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E s)
    (Gamma : Fin q → Finset (Point N k × ZMod N))
    (hGamma : ∀ i, MultiplyLinearWith Q E (Gamma i)) :
    MultiplyLinearWith (fun s => (q : Real) * Q (s / q)) (fun s => E (s / q) ^ q)
      (section16FinsetUnion Gamma) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  refine (MultiplyLinearWith.fin_union hQ hE m Gamma hGamma).congr_controls ?_ ?_
  · intro s _ _
    show ((m : Real) + 1) * Q (s / ((m : Real) + 1)) =
      ((m + 1 : Nat) : Real) * Q (s / ((m + 1 : Nat) : Real))
    first | norm_num | (push_cast; ring) | simp
  · intro s _ _
    show E (s / ((m : Real) + 1)) ^ (m + 1) = E (s / ((m + 1 : Nat) : Real)) ^ (m + 1)
    first | norm_num | (push_cast; ring) | simp

end LeanProofs.GowersSzemeredi
