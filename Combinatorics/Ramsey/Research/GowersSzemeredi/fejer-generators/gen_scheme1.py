"""Slice schemes, level 1: one line-cell lemma for local-piece and joint-slice sections.

`single_piece_on_line_cell_of_slices` (local piece providers, one section after the other) and
`single_piece_on_line_cell_of_joint_slices` (the two sections covered jointly) share steps 1, 2, 4
and 5. `SliceScheme` packages step 3; `single_piece_on_line_cell_of_scheme` is the common proof and
both printed lemmas are its instances (`localPieceScheme`, `jointSliceScheme`).
"""
from foldlib import Fold

SS, JC = 'Proofs16SinglePieceSections', 'Proofs16JointSliceCell'
F = Fold()


def sub1(t, a, b):
    assert t.count(a) == 1, (t.count(a), a[:80])
    return t.replace(a, b)


single = F.take(SS, 'single_piece_on_line_cell_of_slices')
g = single
g = sub1(g, '/-- **One multilinear piece on a line-covered cell**, from providers for the\n'
            'cross-sections `φ(·, x)`. -/\n'
            'theorem single_piece_on_line_cell_of_slices {k q : Nat} (hk : 0 < k)\n'
            '    {c : Real → Real} {w : Real → Nat → Nat}\n'
            '    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))\n'
            '    {N : Nat} [NeZero N] [Fact N.Prime]\n',
         '/-- **One multilinear piece on a line-covered cell**, for cross-sections\n'
         '`φ(·, x)` satisfying the slice condition of a scheme. -/\n'
         'theorem single_piece_on_line_cell_of_scheme {k q : Nat} (hk : 0 < k)\n'
         '    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)\n')
g = sub1(g, '(hsl : ∀ x ∈ J.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))',
         '(hsl : ∀ x ∈ J.carrier, Sc.SL (Dom x) (fun h => phi (h, x)))')
g = sub1(g, '(hwidth : 2 ≤ w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width)) :',
         '(hwidth : 2 ≤ Sc.wid (singlePieceTheta theta q) T.width) :')
g = sub1(g, '      Nat.sqrt (w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width) - 1) - 1\n'
            '        ≤ S.width ∧\n',
         '      Nat.sqrt (Sc.wid (singlePieceTheta theta q) T.width - 1) - 1 ≤ S.width ∧\n')
g = sub1(g, '      singlePieceDensity c theta q * S.carrier.card ≤\n',
         '      singlePieceTheta theta q * Sc.dens (singlePieceTheta theta q) * S.carrier.card ≤\n')
step3_old = g[g.index('  -- 3. the cross-section at `a`, then at `b`\n'):g.index('  have hR2two : 2 ≤ R2.width')]
g = sub1(g, step3_old,
         '  -- 3. both cross-sections, by the scheme\n'
         '  obtain ⟨R2, mua, mub, hR2, hR2T, hR2width, hmua, hmub, hR2c⟩ :=\n'
         '    Sc.step θ1 hθ1pos hθ1le T H1 (Dom a) (Dom b) _ _ hT hTne (Finset.filter_subset _ _)\n'
         '      (fun h hh => hDom _ (hslice h hh).1) (fun h hh => hDom _ (hslice h hh).2) hH1\n'
         '      (hsl a ha) (hsl b hb)\n'
         '  set H3 := H1.filter fun x => x ∈ R2.carrier ∧ phi (x, a) = mua x ∧ phi (x, b) = mub x\n'
         '    with hH3def\n'
         '  have hR2c : Sc.dens θ1 * R2.carrier.card ≤ H3.card := hR2c\n')
g = sub1(g, '    obtain ⟨hpH2, -, hb\'⟩ := Finset.mem_filter.mp hpH3\n'
            '    obtain ⟨-, -, ha\'⟩ := Finset.mem_filter.mp hpH2\n',
         '    obtain ⟨-, -, ha\', hb\'⟩ := Finset.mem_filter.mp hpH3\n')
g = sub1(g, '  have hGcard : c (c θ1) * R2.carrier.card * (θ1 * J.carrier.card) ≤ G.card := by\n'
            '    have h := fibre_sum_ge W H3 (s := θ1 * J.carrier.card) fun h hh =>\n'
            '      (Finset.mem_filter.mp (Finset.filter_subset _ _ (Finset.filter_subset _ _ hh))).2\n',
         '  have hGcard : Sc.dens θ1 * R2.carrier.card * (θ1 * J.carrier.card) ≤ G.card := by\n'
         '    have h := fibre_sum_ge W H3 (s := θ1 * J.carrier.card) fun h hh =>\n'
         '      (Finset.mem_filter.mp (Finset.filter_subset _ _ hh)).2\n')
g = sub1(g, 'R2.axis_carrier_subset_of_carrier_subset T hR2ne (hR2R1.trans hR1T) i',
         'R2.axis_carrier_subset_of_carrier_subset T hR2ne hR2T i')
g = sub1(g, '    have hc2pos := (hc (c θ1) hcpos hcle).1\n', '    have hc2pos := Sc.dens_pos θ1 hθ1pos hθ1le\n')
g = sub1(g, '  have hle : ∑ j, singlePieceDensity c theta q * (S j).carrier.card ≤ ∑ j, ((Gj j).card : Real) := by\n'
            '    rw [← Finset.mul_sum, hSsum, hGsum]\n'
            '    calc singlePieceDensity c theta q * (R2.carrier.card * J.carrier.card) =\n'
            '        c (c θ1) * R2.carrier.card * (θ1 * J.carrier.card) := by\n'
            '          rw [singlePieceDensity, ← hθ1def]; ring\n',
         '  have hle : ∑ j, θ1 * Sc.dens θ1 * (S j).carrier.card ≤ ∑ j, ((Gj j).card : Real) := by\n'
         '    rw [← Finset.mul_sum, hSsum, hGsum]\n'
         '    calc θ1 * Sc.dens θ1 * (R2.carrier.card * J.carrier.card) =\n'
         '        Sc.dens θ1 * R2.carrier.card * (θ1 * J.carrier.card) := by ring\n')
g = sub1(g, '  refine ⟨S j, R2, I j, mu, (hSprop j).1, hSprod j, hR2R1.trans hR1T, ?_, ?_, hmu, ?_⟩',
         '  refine ⟨S j, R2, I j, mu, (hSprop j).1, hSprod j, hR2T, ?_, ?_, hmu, ?_⟩')
g = sub1(g, '    exact ⟨hR1T (hR2R1 hx\'.1), hx\'.2⟩', '    exact ⟨hR2T hx\'.1, hx\'.2⟩')
g = sub1(g, '  · have hsq : Nat.sqrt (w (c θ1) (w θ1 T.width) - 1) ≤ v :=',
         '  · have hsq : Nat.sqrt (Sc.wid θ1 T.width - 1) ≤ v :=')

SCHEME = '''/-! ### Slice schemes

The line-cell argument uses the cross-sections `φ(·, x)` in one step only: on
a dense set `H` of a box `T` whose sections at two anchors satisfy the slice
condition, it needs a sub-box on which a fixed fraction of `H` agrees with a
multilinear function at both anchors (Notes L.16q). A slice scheme packages
that step together with its width and density. `localPieceScheme` uses local
piece providers, one section after the other; `jointSliceScheme`
(`Proofs16JointSliceCell`) covers both sections at once. -/

/-- A slice condition with the width and the density of its two-section step. -/
structure SliceScheme (N k : Nat) [NeZero N] where
  /-- The condition on a cross-section `g` with domain `D`. -/
  SL : Finset (Point N k) → (Point N k → ZMod N) → Prop
  /-- The width of the two-section box at density `θ`, from the width `L` of the box. -/
  wid : Real → Nat → Nat
  /-- The fraction of the dense set that agrees at both sections. -/
  dens : Real → Real
  wid_mono : ∀ θ : Real, 0 < θ → θ ≤ 1 → Monotone (wid θ)
  dens_pos : ∀ θ : Real, 0 < θ → θ ≤ 1 → 0 < dens θ
  step : ∀ θ : Real, 0 < θ → θ ≤ 1 → ∀ (T : Box N k) (H Da Db : Finset (Point N k))
    (ga gb : Point N k → ZMod N), T.IsProper → T.carrier.Nonempty → H ⊆ T.carrier → H ⊆ Da →
    H ⊆ Db → θ * T.carrier.card ≤ H.card → SL Da ga → SL Db gb →
    ∃ (R : Box N k) (ma mb : Point N k → ZMod N), R.IsProper ∧ R.carrier ⊆ T.carrier ∧
      wid θ T.width ≤ R.width ∧ IsMultilinear ma ∧ IsMultilinear mb ∧
      dens θ * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ ga x = ma x ∧ gb x = mb x).card

theorem SliceScheme.congr {N k : Nat} [NeZero N] (Sc : SliceScheme N k)
    {D : Finset (Point N k)} {g g' : Point N k → ZMod N} (h : Sc.SL D g)
    (hg : ∀ x, g' x = g x) : Sc.SL D g' := by
  obtain rfl : g' = g := funext hg
  exact h

/-- Local piece providers, applied to the first section and then, inside its
agreement set, to the second: width `w (c θ) (w θ L)`, density `c (c θ)`. -/
def localPieceScheme {N k : Nat} [NeZero N] (c : Real → Real) (w : Real → Nat → Nat)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t)) :
    SliceScheme N k where
  SL := LocalPieceFor c w
  wid θ L := w (c θ) (w θ L)
  dens θ := c (c θ)
  wid_mono θ _ _ := (hw _).comp (hw θ)
  dens_pos θ hθ hθ1 := (hc _ (hc θ hθ hθ1).1 (hc θ hθ hθ1).2).1
  step θ hθ hθ1 T H Da Db ga gb hT _ hHT hHa hHb hHc ha hb := by
    obtain ⟨R1, mua, hR1, hR1T, hR1w, hmua, hR1c⟩ := ha θ hθ hθ1 T H hT hHT hHa hHc
    obtain ⟨hcpos, hcle⟩ := hc θ hθ hθ1
    obtain ⟨R2, mub, hR2, hR2R1, hR2w, hmub, hR2c⟩ := hb (c θ) hcpos hcle R1
      (H.filter fun x => x ∈ R1.carrier ∧ ga x = mua x) hR1
      (fun x hx => (Finset.mem_filter.mp hx).2.1)
      (fun x hx => hHb (Finset.filter_subset _ _ hx)) hR1c
    refine ⟨R2, mua, mub, hR2, hR2R1.trans hR1T, (hw _ hR1w).trans hR2w, hmua, hmub,
      hR2c.trans ?_⟩
    exact_mod_cast Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1.1, hx.2.1, hx.1.2.2, hx.2.2⟩

'''
INST1 = '''/-- **One multilinear piece on a line-covered cell**, from providers for the
cross-sections `φ(·, x)`. -/
theorem single_piece_on_line_cell_of_slices {k q : Nat} (hk : 0 < k)
    {c : Real → Real} {w : Real → Nat → Nat}
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {N : Nat} [NeZero N] [Fact N.Prime]
'''
# the printed lemma keeps its statement: its binders after `[Fact N.Prime]` are those of the generic
sig_rest = single[single.index('    (T : Box N k) (J : ModAP N)'):single.index(':= by')]
INST1 += sig_rest + ''':=
  single_piece_on_line_cell_of_scheme hk (localPieceScheme c w hc hw) T J hT hJ hTne hTd hJstep
    hshort hTJ D hD hθ hθ1 hq hDc hJq cls phi ell hell hphi Dom hsl hDom hwidth
'''
F.insert(SS, SCHEME + g + '\n' + INST1, 'single_piece_on_line_cell')
F.commit()
