"""Slice schemes, level 2: the affine-cell and spectrum-cover lemmas for any slice scheme.

`single_piece_on_affine_cell(_joint)` and `single_piece_of_spectrum_cover_for(_joint)` become
instances of `…_of_scheme` / `…_for_scheme` at `localPieceScheme` and `jointSliceScheme`.
"""
from foldlib import Fold

SP, JS = 'Proofs16SinglePieceSpectrum', 'Proofs16JointSliceSpectrum'
F = Fold()


def sub1(t, a, b):
    assert t.count(a) == 1, (t.count(a), a[:90])
    return t.replace(a, b)


# --- affine cell
aff = F.take(SP, 'single_piece_on_affine_cell')
g = aff
g = sub1(g, '/-- **Step 2 with affine fibres** (one class, `q = 1`). -/\n'
            'theorem single_piece_on_affine_cell {k : Nat} (hk : 0 < k)\n'
            '    {c : Real → Real} {w : Real → Nat → Nat}\n'
            '    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))\n'
            '    {N : Nat} [NeZero N] [Fact N.Prime]\n',
         '/-- **Step 2 with affine fibres** (one class, `q = 1`), for a slice scheme. -/\n'
         'theorem single_piece_on_affine_cell_of_scheme {k : Nat} (hk : 0 < k)\n'
         '    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)\n')
g = sub1(g, '(hsl : ∀ x ∈ J.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))',
         '(hsl : ∀ x ∈ J.carrier, Sc.SL (Dom x) (fun h => phi (h, x)))')
g = sub1(g, '(hwidth : 2 ≤ w (c (singlePieceTheta theta 1)) (w (singlePieceTheta theta 1) T.width)) :',
         '(hwidth : 2 ≤ Sc.wid (singlePieceTheta theta 1) T.width) :')
g = sub1(g, '      Nat.sqrt (w (c (singlePieceTheta theta 1)) (w (singlePieceTheta theta 1) T.width) - 1) - 1\n'
            '        ≤ S.width ∧\n',
         '      Nat.sqrt (Sc.wid (singlePieceTheta theta 1) T.width - 1) - 1 ≤ S.width ∧\n')
g = sub1(g, '      singlePieceDensity c theta 1 * S.carrier.card ≤\n',
         '      singlePieceTheta theta 1 * Sc.dens (singlePieceTheta theta 1) * S.carrier.card ≤\n')
g = sub1(g, 'refine single_piece_on_line_cell_of_slices hk hc hw T J', 'refine single_piece_on_line_cell_of_scheme hk Sc T J')
aff_inst = aff[:aff.index(':= by')] + ''':=
  single_piece_on_affine_cell_of_scheme hk (localPieceScheme c w hc hw) T J hT hJ hTne hTd hJstep
    hshort hTJ D hD hθ hθ1 hDc hJq phi haff Dom hsl hDom hwidth
'''
F.insert(SP, g + '\n' + aff_inst, 'spectrumPieceRho')

# --- spectrum cover
spec = F.take(SP, 'single_piece_of_spectrum_cover_for')
g = spec
g = sub1(g, 'theorem single_piece_of_spectrum_cover_for {k : Nat} (hk : 0 < k)',
         'theorem single_piece_of_spectrum_cover_for_scheme {k : Nat} (hk : 0 < k)')
g = sub1(g, '    {wR : Real → Nat → Nat} {c : Real → Real} {w : Real → Nat → Nat}\n',
         '    {wR : Real → Nat → Nat}\n')
g = sub1(g, '    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))\n', '')
g = sub1(g, '    {N : Nat} [NeZero N] [Fact N.Prime]\n', '    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)\n')
g = sub1(g, '(hsl : ∀ x ∈ J0.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))',
         '(hsl : ∀ x ∈ J0.carrier, Sc.SL (Dom x) (fun h => phi (h, x)))')
g = sub1(g, '      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR theta) 1))\n'
            '        (w (singlePieceTheta (spectrumPieceRho cR theta) 1)\n'
            '          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊)) :\n',
         '      2 ≤ Sc.wid (singlePieceTheta (spectrumPieceRho cR theta) 1)\n'
         '        ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) :\n')
g = sub1(g, '        Nat.sqrt (w (c (singlePieceTheta (spectrumPieceRho cR theta) 1))\n'
            '          (w (singlePieceTheta (spectrumPieceRho cR theta) 1)\n'
            '            ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) - 1) - 1 ≤ S.width ∧\n',
         '        Nat.sqrt (Sc.wid (singlePieceTheta (spectrumPieceRho cR theta) 1)\n'
         '          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊ - 1) - 1 ≤ S.width ∧\n')
g = sub1(g, '        singlePieceDensity c (spectrumPieceRho cR theta) 1 * S.carrier.card ≤\n',
         '        singlePieceTheta (spectrumPieceRho cR theta) 1 *\n'
         '            Sc.dens (singlePieceTheta (spectrumPieceRho cR theta) 1) * S.carrier.card ≤\n')
g = sub1(g, '  have hwidth : 2 ≤ w (c (singlePieceTheta ρ 1)) (w (singlePieceTheta ρ 1) (Q l).width) :=\n'
            '    hcellw.trans (hw _ (hw _ hQw))\n',
         '  have hθ₁ := singlePieceTheta_pos hρpos one_pos\n'
         '  have hθ₁1 := singlePieceTheta_le_one hρpos hρle one_pos\n'
         '  have hwidth : 2 ≤ Sc.wid (singlePieceTheta ρ 1) (Q l).width :=\n'
         '    hcellw.trans (Sc.wid_mono _ hθ₁ hθ₁1 hQw)\n')
g = sub1(g, 'single_piece_on_affine_cell hk hc hw (Q l) I', 'single_piece_on_affine_cell_of_scheme hk Sc (Q l) I')
g = sub1(g, '      (hw (c (singlePieceTheta ρ 1)) (hw (singlePieceTheta ρ 1) hQw)) 1)',
         '      (Sc.wid_mono _ hθ₁ hθ₁1 hQw) 1)')
spec_inst = spec[:spec.index(':= by')] + ''':=
  single_piece_of_spectrum_cover_for_scheme hk hcR eps thr hretile hz hz2 (localPieceScheme c w hc hw)
    T0 J0 hT0 hJ0 hT0d hJ0step hshort hT0J0 hJ0pos E hE hθ hθ1 hEc phi f s Mrem hMrem hident Gamma
    DomG hcover hEG K hK A hA hlinear Dom hsl hDom m hm1 hm hpar
'''
F.insert(SP, g + '\n' + spec_inst, 'single_piece_of_spectrum_cover')

# --- joint instances
F.reprove(JS, 'single_piece_on_affine_cell_joint', '''
  single_piece_on_affine_cell_of_scheme hk (jointSliceScheme Qs Es hQs hEs) T J hT hJ hTne hTd
    hJstep hshort hTJ D hD hθ hθ1 hDc hJq phi haff Dom hsl hDom hwidth''')
F.reprove(JS, 'single_piece_of_spectrum_cover_for_joint', '''
  single_piece_of_spectrum_cover_for_scheme hk hcR eps thr hretile hz hz2
    (jointSliceScheme Qs Es hQs hEs) T0 J0 hT0 hJ0 hT0d hJ0step hshort hT0J0 hJ0pos E hE hθ hθ1 hEc
    phi f s Mrem hMrem hident Gamma DomG hcover hEG K hK A hA hlinear Dom hsl hDom m hm1 hm hpar''')
F.commit()
