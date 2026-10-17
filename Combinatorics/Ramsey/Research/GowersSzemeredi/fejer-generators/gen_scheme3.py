"""Slice schemes, level 3: `single_piece_lift_core_rem` for any slice scheme.

The local-piece and joint-slice core lifts become instances of `single_piece_lift_core_rem_scheme`.
"""
from foldlib import Fold

SG, JC = 'Proofs16SinglePieceGlobal', 'Proofs16JointSliceCore'
F = Fold()


def sub1(t, a, b):
    assert t.count(a) == 1, (t.count(a), a[:90])
    return t.replace(a, b)


core = F.take(SG, 'single_piece_lift_core_rem')
g = core
g = sub1(g, 'theorem single_piece_lift_core_rem {k : Nat}', 'theorem single_piece_lift_core_rem_scheme {k : Nat}')
g = sub1(g, '    {c : Real → Real} {w : Real → Nat → Nat}\n', '')
g = sub1(g, '    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))\n', '')
g = sub1(g, '    {N : Nat} [NeZero N] [Fact N.Prime]\n', '    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)\n')
g = sub1(g, '(hsl : ∀ x, LocalPieceFor c w (DomS x) (fun h => phi (appendCoordinate (h + x0) x)))',
         '(hsl : ∀ x, Sc.SL (DomS x) (fun h => phi (appendCoordinate (h + x0) x)))')
g = sub1(g, '      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1))\n'
            '        (w (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)\n'
            '          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊)) :\n',
         '      2 ≤ Sc.wid (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)\n'
         '        ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) :\n')
g = sub1(g, '        Nat.sqrt (w (c (singlePieceTheta\n'
            '            (spectrumPieceRho cR (ρ1)) 1))\n'
            '          (w (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)\n'
            '            ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) - 1) - 1 ≤ S.width ∧\n',
         '        Nat.sqrt (Sc.wid (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)\n'
         '          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊ - 1) - 1 ≤ S.width ∧\n')
g = sub1(g, '        singlePieceDensity c (spectrumPieceRho cR (ρ1)) 1 *\n            S.carrier.card ≤\n',
         '        singlePieceTheta (spectrumPieceRho cR (ρ1)) 1 *\n'
         '            Sc.dens (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1) * S.carrier.card ≤\n')
g = sub1(g, "  have hsl' : ∀ x ∈ I.carrier, LocalPieceFor c w (DomS x) (fun h => phi1 (h, x)) := by",
         "  have hsl' : ∀ x ∈ I.carrier, Sc.SL (DomS x) (fun h => phi1 (h, x)) := by")
g = sub1(g, '    refine (hsl x).congr rfl (fun h => ?_)', '    refine Sc.congr (hsl x) (fun h => ?_)')
g = sub1(g, '    single_piece_of_spectrum_cover_for hk0 hcR hc hw eps thr hretile hz hz2',
         '    single_piece_of_spectrum_cover_for_scheme hk0 hcR eps thr hretile hz hz2 Sc')
inst = core[:core.index(':= by')] + ''':=
  single_piece_lift_core_rem_scheme hk hz hz2 hcR hwR eps thr hretile (localPieceScheme c w hc hw) B
    phi H Y phiPrime x0 hselection hid B1 hB1 hθ₂pos hθ₂le hB1card ρ1 hρ1 ω1 hrem DomG hcovG hB1G
    DomS hsl hB1S hL4 m hm1 hm hpar
'''
F.insert(SG, g + '\n' + inst, 'single_piece_lift_core')
F.reprove(JC, 'single_piece_lift_core_rem_joint', '''
  single_piece_lift_core_rem_scheme hk hz hz2 hcR hwR eps thr hretile (jointSliceScheme Qs Es hQs hEs)
    B phi H Y phiPrime x0 hselection hid B1 hB1 hθ₂pos hθ₂le hB1card ρ1 hρ1 ω1 hrem DomG hcovG hB1G
    DomS hsl hB1S hL4 m hm1 hm hpar''')
F.commit()
