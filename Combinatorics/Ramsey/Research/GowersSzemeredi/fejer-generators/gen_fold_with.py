"""Fold the five `…With` modules of Notes L.16d into their originals (refactor map, L.16e).

Each parametric theorem moves in front of its printed original, whose proof becomes the instance at
`t1 = section16ThetaOne θ γ k`, `ζ = section16Zeta θ γ k` (`lemma_16_5_with_printed_hyps`).
Printed statements are unchanged.
"""
from foldlib import Fold

F = Fold()
PH = 'have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1\n'

# --- Lemma5With
F.move('Proofs16Lemma5With', ['section16_good_sidelengths_with'],
       'Proofs16ArrangementSelection', 'section16_good_sidelengths_of_arrangements')
F.reprove('Proofs16ArrangementSelection', 'section16_good_sidelengths_of_arrangements',
          '\n  section16_good_sidelengths_with _ B phi (by unfold section16ThetaOne; positivity) hB')
F.move('Proofs16Lemma5With', ['lemma_16_5_with_printed_hyps', 'section16_selected_side_model_with'],
       'Proofs16Lemma5', 'section16_selected_side_model')
F.reprove('Proofs16Lemma5', 'section16_selected_side_model',
          '\n  ' + PH + '  section16_selected_side_model_with _ _ B phi h hp.1 hp.2.1 hp.2.2 hcount happrox')
F.move('Proofs16Lemma5With', ['lemma_16_5_with'], 'Proofs16Lemma5', 'lemma_16_5_holds')
F.reprove('Proofs16Lemma5', 'lemma_16_5_holds',
          ' by\n  intro N k _ theta gamma B phi ht ht1 hg hg1 hB\n  ' + PH +
          '  exact lemma_16_5_with _ _ B phi hp.1 hp.2.1 hp.2.2 hB.2')
F.move('Proofs16Lemma5With', ['tightZeta_condition'], 'Proofs16TightRadius')
F.delete_module('Proofs16Lemma5With', ['Proofs16Lemma5', 'Proofs16TightRadius'])
F.doc_append('Proofs16ArrangementSelection',
             '`section16_good_sidelengths_with` takes the density `t1` as a parameter;\n'
             '`section16_good_sidelengths_of_arrangements` is its printed instance.')
F.doc_append('Proofs16Lemma5',
             '`section16_selected_side_model_with` and `lemma_16_5_with` take the density\n'
             'and the radius `(t1, ζ)` as parameters, under `0 < t1/4 ≤ 1/36` and\n'
             '`ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6` (Notes L.16d). The printed values\n'
             'satisfy these (`lemma_16_5_with_printed_hyps`), and the printed results are\n'
             'the instances.')

# --- DenseSelectionWith
F.move('Proofs16DenseSelectionWith', ['section16_dense_induced_selection_with'],
       'Proofs16DenseSelection', 'section16_dense_induced_selection_of_arrangements')
F.reprove('Proofs16DenseSelection', 'section16_dense_induced_selection_of_arrangements',
          '\n  ' + PH + '  section16_dense_induced_selection_with hprime _ _ B phi hp.1 hp.2.1 hp.2.2\n'
          '    (by unfold section16Zeta; positivity) hB')
F.delete_module('Proofs16DenseSelectionWith',
                ['Proofs16DenseSelection', 'Proofs16Lemma5', 'Proofs16TightRadius', 'Proofs16CommonBase'])
F.doc_append('Proofs16DenseSelection',
             '`section16_dense_induced_selection_with` is the selection with `(t1, ζ)` as\n'
             'parameters; the printed one is its instance.')

# --- PolyPieceTwoDataWith
F.move('Proofs16PolyPieceTwoDataWith',
       ['polyPieceBudgetW', 'polyPieceSpecCountW', 'polyPieceFaceCountW', 'polyPieceBudgetW_printed',
        'polyPieceSpecCountW_printed', 'polyPieceFaceCountW_printed', 'section16_theta_delta_bounds_with',
        'section16ThetaTwo_pos_le_with', 'section16_poly_piece_two_data_with'],
       'Proofs16PolyPieceTwoData', 'section16_poly_piece_two_data')
F.reprove('Proofs16PolyPieceTwoData', 'section16_poly_piece_two_data',
          '\n  have hp := lemma_16_5_with_printed_hyps 1 ht ht1 hg hg1\n'
          '  section16_poly_piece_two_data_with hp.1 hp.2.1 hp.2.2 (by unfold section16Zeta; positivity)\n'
          '    hg hg1 Gamma B phi hBG hBarr hprodB')
F.delete_module('Proofs16PolyPieceTwoDataWith',
                ['Proofs16PolyPieceTwoData', 'Proofs16DenseSelection', 'Proofs16Lemma5', 'Proofs16TightRadius',
                 'Proofs16CommonBase'])
F.doc_append('Proofs16PolyPieceTwoData',
             'The budgets `polyPieceBudgetW`, `polyPieceSpecCountW`, `polyPieceFaceCountW` and\n'
             '`section16_poly_piece_two_data_with` take the density `t1` and the radius `ζ`\n'
             'as parameters (Notes L.16d). At the printed values the budgets are the printed\n'
             'ones by `rfl` (`…W_printed`), and `section16_poly_piece_two_data` is the\n'
             'instance.')

# --- ClassPiecesWith
F.move('Proofs16ClassPiecesWith',
       ['classBudgetW', 'classPieceThrW', 'classBudgetW_printed', 'classPieceThrW_printed',
        'classBudgetW_pos_le', 'class_piece_data_with'],
       'Proofs16ClassPieces', 'class_piece_data')
F.reprove('Proofs16ClassPieces', 'class_piece_data',
          '\n  ' + PH + '  class_piece_data_with C hp.1 hp.2.1 hp.2.2 (by unfold section16Zeta; positivity) hg hg1\n'
          '    hN Gamma B phi hBG hBarr hprodB')
F.delete_module('Proofs16ClassPiecesWith',
                ['Proofs16ClassPieces', 'Proofs16DenseSelection', 'Proofs16Lemma5', 'Proofs16TightRadius',
                 'Proofs16CommonBase', 'Proofs16PolyPieceTwoData'])
F.doc_append('Proofs16ClassPieces',
             '`classBudgetW`, `classPieceThrW` and `class_piece_data_with` take `(t1, ζ)` as\n'
             'parameters (Notes L.16d); at the printed values the budgets are the printed\n'
             'ones by `rfl`, and `class_piece_data` is the instance.')

# --- SinglePieceCoverGlobalWith
F.move('Proofs16SinglePieceCoverGlobalWith',
       ['globalBudgetW', 'globalTheta2W', 'coverPrecW', 'coverCountW', 'coverRho1W', 'coverExpW',
        'coverRemWidthW', 'globalBudgetW_printed', 'globalTheta2W_printed', 'coverRho1W_printed',
        'coverRemWidthW_printed', 'globalTheta2W_pos_le', 'coverPrecW_pos_le', 'nonTop_coverPrecW_sum_le',
        'coverCountW_pos', 'one_le_coverCountW', 'coverRho1W_pos_le', 'single_piece_lift_global_cover_with'],
       'Proofs16SinglePieceCoverGlobal', 'single_piece_lift_global_cover')
F.reprove('Proofs16SinglePieceCoverGlobal', 'single_piece_lift_global_cover',
          '\n  ' + PH + '  have hz := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1\n'
          '  single_piece_lift_global_cover_with hk hp.1 hp.2.1 hp.2.2 hz.1 (by linarith [hz.2]) hg hg1\n'
          '    hcov hQb hEb hEb1 eps thr hretile B phi hB hprodB hL4 m hm1 hm hpar')
F.delete_module('Proofs16SinglePieceCoverGlobalWith',
                ['Proofs16SinglePieceCoverGlobal', 'Proofs16DenseSelection', 'Proofs16Lemma5',
                 'Proofs16TightRadius', 'Proofs16CommonBase', 'Proofs16PolyPieceTwoData'])
F.doc_append('Proofs16SinglePieceCoverGlobal',
             'The `…W` parameters and `single_piece_lift_global_cover_with` take `(t1, ζ)`\n'
             'as parameters (Notes L.16d); at the printed values they are the printed ones\n'
             'by `rfl` (`…W_printed`), and `single_piece_lift_global_cover` is the instance.')
s = F.get('Proofs16SinglePieceCoverGlobal')
imp = 'import GowersSzemeredi.Proofs16PolyPieceTwoData\n'
if imp not in s:
    F.text['Proofs16SinglePieceCoverGlobal'] = imp + s
F.commit()
