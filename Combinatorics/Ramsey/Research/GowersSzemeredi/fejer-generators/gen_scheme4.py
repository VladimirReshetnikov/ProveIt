"""Slice schemes, level 4: the global-cover lift for any slice scheme.

The slice conditions come from the face covers of the last-coordinate slices, translated by `x0`;
the scheme only needs a map from such a cover to its slice condition (`hof`). The local-piece and
joint-slice global lifts are the instances.
"""
from foldlib import Fold

SC, JG = 'Proofs16SinglePieceCoverGlobal', 'Proofs16JointSliceGlobal'
F = Fold()


def sub1(t, a, b):
    assert t.count(a) == 1, (t.count(a), a[:90])
    return t.replace(a, b)


WIDE = ('coverWidth (Eb k gamma (globalBudgetW t1 k))\n'
        '          ((fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))\n'
        '            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)\n'
        '              (coverRho1W Qb t1 gamma k)) 1))\n'
        '        (coverWidth (Eb k gamma (globalBudgetW t1 k))\n'
        '          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)\n'
        '            (coverRho1W Qb t1 gamma k)) 1)\n'
        '          ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊)')
TH1 = 'singlePieceTheta (spectrumPieceRho (fun t => t / 2) (coverRho1W Qb t1 gamma k)) 1'
glob = F.take(SC, 'single_piece_lift_global_cover_with')
g = glob
g = sub1(g, 'theorem single_piece_lift_global_cover_with {k : Nat}', 'theorem single_piece_lift_global_cover_scheme {k : Nat}')
g = sub1(g, '    {N : Nat} [NeZero N] [Fact N.Prime]\n',
         '    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)\n'
         '    (hof : ∀ (D J : Finset (Point N k)) (g : Point N k → ZMod N) (t : Point N k),\n'
         '      MultiplyLinearWith (Qb k gamma (globalBudgetW t1 k)) (Eb k gamma (globalBudgetW t1 k))\n'
         '        (restrictRelation (partialGraph D g) J) →\n'
         '      Sc.SL (Finset.univ.filter fun h => h + t ∈ D ∩ J) (fun h => g (h + t)))\n')
g = sub1(g, '      2 ≤ ' + WIDE + ') :\n', f'      2 ≤ Sc.wid ({TH1})\n        ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊) :\n')
g = sub1(g, '        Nat.sqrt (coverWidth (Eb k gamma (globalBudgetW t1 k))\n'
            '          ((fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))\n'
            '            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)\n'
            '              (coverRho1W Qb t1 gamma k)) 1))\n'
            '          (coverWidth (Eb k gamma (globalBudgetW t1 k))\n'
            '            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)\n'
            '              (coverRho1W Qb t1 gamma k)) 1)\n'
            '            ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊) - 1) - 1 ≤\n',
         f'        Nat.sqrt (Sc.wid ({TH1})\n          ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊ - 1) - 1 ≤\n')
g = sub1(g, '        singlePieceDensity (fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))\n'
            '            (spectrumPieceRho (fun t => t / 2)\n'
            '              (coverRho1W Qb t1 gamma k)) 1 *\n',
         f'        {TH1} *\n            Sc.dens ({TH1}) *\n')
g = sub1(g, '  have hsl : ∀ x, LocalPieceFor (fun s => s / 2 / Qb k gamma θ\' (s / 2))\n'
            '      (coverWidth (Eb k gamma θ\')) (DomS x) (fun h => phi (appendCoordinate (h + x0) x)) :=\n'
            '    fun x => ((hMLs x).localPieceFor (hQb k gamma θ\') (hEb k gamma θ\')).translate x0\n',
         '  have hsl : ∀ x, Sc.SL (DomS x) (fun h => phi (appendCoordinate (h + x0) x)) :=\n'
         '    fun x => hof _ _ _ x0 (hMLs x)\n')
g = sub1(g, '  have hc : ∀ s : Real, 0 < s → s ≤ 1 → 0 < s / 2 / Qb k gamma θ\' (s / 2) ∧\n'
            '      s / 2 / Qb k gamma θ\' (s / 2) ≤ 1 := by\n'
            '    intro s hs hs1\n'
            '    have hq := hQb k gamma θ\' (s / 2) (by positivity) (by linarith)\n'
            '    refine ⟨by positivity, ?_⟩\n'
            '    rw [div_le_one (by linarith)]\n'
            '    linarith\n', '')
g = sub1(g, '  exact single_piece_lift_core_rem hk hz0 hz2', '  exact single_piece_lift_core_rem_scheme hk hz0 hz2')
g = sub1(g, '    hc (coverWidth_mono _) eps thr hretile B phi H Y phiPrime x0 hselection hid B1\'\n',
         '    eps thr hretile Sc B phi H Y phiPrime x0 hselection hid B1\'\n')
ARGS = 'hk ha0 haS hzeta hz0 hz2 hg hg1 hcov hQb hEb hEb1 eps thr hretile'
TAIL = 'B phi hB hprodB hL4 m hm1 hm hpar'
inst = glob[:glob.index(':= by')] + f''':= by
  have hc : ∀ s : Real, 0 < s → s ≤ 1 → 0 < s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2) ∧
      s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2) ≤ 1 := by
    intro s hs hs1
    have hq := hQb k gamma (globalBudgetW t1 k) (s / 2) (by positivity) (by linarith)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  exact single_piece_lift_global_cover_scheme {ARGS}
    (localPieceScheme (fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))
      (coverWidth (Eb k gamma (globalBudgetW t1 k))) hc (coverWidth_mono _))
    (fun _ _ _ t h => (h.localPieceFor (hQb k gamma _) (hEb k gamma _)).translate t) {TAIL}
'''
F.insert(SC, g + '\n' + inst, 'single_piece_lift_global_cover')
F.reprove(JG, 'single_piece_lift_global_cover_with_joint', f'''
  single_piece_lift_global_cover_scheme {ARGS}
    (jointSliceScheme (Qb k gamma (globalBudgetW t1 k)) (Eb k gamma (globalBudgetW t1 k))
      (hQb k gamma _) fun t ht ht1 => (hEb k gamma _ t ht ht1).le)
    (fun _ _ _ t h => by rw [restrictRelation_partialGraph] at h; exact h.translate_graph t) {TAIL}''')
F.commit()
