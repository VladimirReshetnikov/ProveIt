"""Proofs15FejerSelection: share the 26 hyperedge/parity/injectivity helpers with Proofs15Restriction.

They were copied because they are private in Proofs15Restriction. The originals become public, the
copies are deleted and every use is renamed (fejer… ↦ selection…). No other module mentions the
selection names, so no public name collides.
"""
import re

from foldlib import Fold

PAIRS = [('fejerIndex', 'selectionIndex'), ('fejerVertex', 'selectionVertex'),
         ('fejerCarrier', 'selectionCarrier'), ('fejerCarrier_subset', 'selectionCarrier_subset'),
         ('fejer_isIn_iff', 'selection_isIn_iff'), ('fejerArrangements', 'selectionArrangements'),
         ('fejerGoodArrangements', 'selectionGoodArrangements'),
         ('fejerBadArrangements', 'selectionBadArrangements'),
         ('fejerArrangements_card', 'selectionArrangements_card'),
         ('fejerGoodArrangements_card', 'selectionGoodArrangements_card'),
         ('fejer_good_restrict_card', 'selection_good_restrict_card'),
         ('fejer_good_bad_restrict_card', 'selection_good_bad_restrict_card'),
         ('fejerIndexSign', 'selectionIndexSign'), ('fejer_additive_iff', 'selection_additive_iff'),
         ('FejerFeature', 'SelectionFeature'), ('FejerPhase', 'SelectionPhase'),
         ('fejer_index_card', 'selection_index_card'), ('fejerFeatureValue', 'selectionFeatureValue'),
         ('fejer_expect_phase', 'selection_expect_phase'), ('fejerEtaZero', 'selectionEtaZero'),
         ('fejerEtaZero_cast', 'selectionEtaZero_cast'), ('fejerEtaZero_cases', 'selectionEtaZero_cases'),
         ('fejerEtaZero_moment', 'selectionEtaZero_moment'), ('fejer_third_index', 'selection_third_index'),
         ('fejer_injective_of_nondegenerate', 'selection_injective_of_nondegenerate'),
         ('fejerCarrier_prod_of_nondegenerate', 'selectionCarrier_prod_of_nondegenerate')]
FS, R = 'Proofs15FejerSelection', 'Proofs15Restriction'
F = Fold()
for f, _ in PAIRS:
    F.delete_decl(FS, f)
s = F.get(FS)
ren = dict(PAIRS)
s = re.sub(r"(?<![\w'.])(" + '|'.join(sorted(map(re.escape, ren), key=len, reverse=True)) + r")(?![\w'])",
           lambda m: ren[m.group(1)], s)
old = ('The hyperedge\nbookkeeping, parity moment and vertex injectivity are copied from\n'
       '`Proofs15Restriction` (private there). -/')
assert old in s, 'docstring'
s = s.replace(old, 'The hyperedge\nbookkeeping, parity moment and vertex injectivity are those of\n'
                   '`Proofs15Restriction`. -/')
F.text[FS] = s
r = F.get(R)
for _, g in PAIRS:
    pat = re.compile(r'^private ((?:noncomputable )?(?:lemma|theorem|def|abbrev) ' + re.escape(g) + r"(?![\w']))", re.M)
    r, n = pat.subn(r'\1', r)
    assert n == 1, (g, n)
F.text[R] = r
F.commit()
