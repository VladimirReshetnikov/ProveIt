"""Slice schemes, level 1 (joint side): `jointSliceScheme`, and the joint line-cell lemma as its
instance of `single_piece_on_line_cell_of_scheme`."""
from foldlib import Fold

JC = 'Proofs16JointSliceCell'
F = Fold()
SCHEME = '''/-- The two sections covered jointly at the common precision `θ/4`
(`joint_cover_on`, then one pigeonhole by `JointCoverOn.piece`): width
`⌈L^(Eb(θ/4)²)⌉`, density `(θ − θ/2)/Qb(θ/4)²`. -/
def jointSliceScheme {N k : Nat} [NeZero N] (Qb Eb : Real → Real)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 1 ≤ Qb t) (hE : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Eb t) :
    SliceScheme N k where
  SL D g := MultiplyLinearWith Qb Eb (partialGraph D g)
  wid θ L := ⌈(L : Real) ^ (Eb (θ / 4) * Eb (θ / 4))⌉₊
  dens θ := (θ - (θ / 4 + θ / 4)) / (Qb (θ / 4) * Qb (θ / 4))
  wid_mono θ hθ hθ1 L1 L2 h := by
    have he := hE (θ / 4) (by positivity) (by linarith)
    exact Nat.ceil_le_ceil
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (mul_nonneg he he))
  dens_pos θ hθ hθ1 := by
    have hQ1 := hQ (θ / 4) (by positivity) (by linarith)
    exact div_pos (by linarith) (by nlinarith)
  step θ hθ hθ1 T H Da Db ga gb hT hTne hHT hHa hHb hHc ha hb := by
    have hρ0 : 0 < θ / 4 := by positivity
    have hρ1 : θ / 4 ≤ 1 := by linarith
    have hJC := joint_cover_on (ι := Bool) (fun e => bif e then Da else Db)
      (fun e => bif e then ga else gb) (fun _ => Qb) (fun _ => Eb) (fun _ => θ / 4) Finset.univ
      (fun e _ => by cases e <;> assumption) (fun _ _ => ⟨hρ0, hρ1⟩)
      (fun _ _ => zero_le_one.trans (hQ _ hρ0 hρ1)) (fun _ _ => hE _ hρ0 hρ1) T hT
    simp only [Fintype.sum_bool, Fintype.prod_bool] at hJC
    obtain ⟨R, nu, hR, hRT, hRw, hnu, hRc⟩ := hJC.piece (theta := θ) (by linarith) H hHT
      (fun e _ => by cases e <;> assumption) hHc hTne
    refine ⟨R, nu true, nu false, hR, hRT, Nat.ceil_le.mpr hRw, hnu _ (Finset.mem_univ _),
      hnu _ (Finset.mem_univ _), hRc.trans ?_⟩
    exact_mod_cast Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, forall_const, Bool.forall_bool, cond_false,
        cond_true] at hx ⊢
      exact ⟨hx.1, hx.2.1, hx.2.2.2, hx.2.2.1⟩

'''
s = F.get(JC)
F.insert(JC, SCHEME, 'single_piece_on_line_cell_of_joint_slices')
F.reprove(JC, 'single_piece_on_line_cell_of_joint_slices', '''
  single_piece_on_line_cell_of_scheme hk (jointSliceScheme Qb Eb hQ hE) T J hT hJ hTne hTd hJstep
    hshort hTJ D hD hθ hθ1 hq hDc hJq cls phi ell hell hphi Dom hsl hDom hwidth''')
F.commit()
