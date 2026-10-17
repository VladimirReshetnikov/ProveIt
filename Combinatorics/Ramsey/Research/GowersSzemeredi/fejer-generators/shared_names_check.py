"""Every name the folds make shared must be declared exactly once in the corpus (public or private).

A private declaration with the short name of an imported public one makes later references ambiguous;
the duplicate gate only sees public names, so this checks all declarations by text.
usage: python -X utf8 shared_names_check.py
"""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
NAMES = ['prop121B', 'prop121_fourthB_eq_weight', 'centeredAbs_neg', 'centeredAbs_nsmul_le',
         'bohr_symmetric_multiples_subset', 'generic_freiman_map_nat_multiple',
         'generic_freiman_map_int_multiple', 'stage136_common_step_mem_bohr_at',
         'lemma_13_6_of_bohr_models_at', 'lemma_13_6_from_initial_stages_at', 'IsStage135At',
         'isStage135Data_iff_at', 'stage135_singleton_at', 'IsPartition.sigma', 'small_fibre_count_le',
         'cor57_norm_exponential_sub_one_le', 'norm_exponential_sub_one_le_two', 'bohr_phase_bound',
         'prop61G', 'prop61QuadMem', 'prop61AltAdditive', 'prop61_alt_count_eq', 'prop61_g_product',
         'prop61_sum_g_product', 'prop61_g_fourth_eq_count']
HD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected )?(?:noncomputable )?"
                r"(?:theorem|lemma|def|abbrev|structure|instance|alias|inductive|class)\s+([^\s(:{\[]+)", re.M)
where = {n: [] for n in NAMES}
for p in GS.glob('*.lean'):
    for h in HD.finditer(p.read_text(encoding='utf8')):
        if h.group(2) in where:
            where[h.group(2)].append(f'{p.stem}{" (private)" if h.group(1) else ""}')
bad = {n: w for n, w in where.items() if len(w) != 1}
for n, w in where.items():
    print(f'{n:40} {" ".join(w)}')
print('PROBLEMS:', bad if bad else 'none')
