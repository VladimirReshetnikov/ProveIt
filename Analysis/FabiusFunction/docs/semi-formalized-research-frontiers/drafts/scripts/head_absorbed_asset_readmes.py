# -*- coding: utf-8 -*-
r"""Head every preserved asset README with where its package went.

The absorbed reports' own package READMEs are kept under assets/ because they
document the scripts and data that sit beside them.  Their build instructions,
however, name a .tex that the consolidation deleted, so a reader who follows
them chases a file that is not there.  Each README now opens with one short
block saying which part absorbed the package and that the source is in git
history; the original text follows unchanged.
"""
import io, os, re, sys

ROOT = (r"C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Analysis"
        r"\FabiusFunction\docs\semi-formalized-research-frontiers\drafts"
        r"\exponents-and-q-series\geometric_q_fabius_frontiers\assets")

PART = {
    'Fabius_Newton_Rvachev_Frontier_Report': 'I',
    'fabius_frontier_results': 'II',
    'finite_sinc_products_report': 'III',
    'Rvachev_Piecewise_Approximation_Fourier_Images': 'IV',
    'rvachev_fourier_frontier_report': 'IV',
    'fabius_finite_products_frontier': 'V',
    'atomic_sinc_splines_report_package': 'VI',
    'Atomic_Functions_Beyond_Dyadic_Report': 'VI',
    'Atomic_Functions_Beyond_Dyadic_Report-2': 'VI',
    'Atomic_Functions_Beyond_Dyadic_Report-3': 'VI',
    'Atomic_Functions_Beyond_Dyadic_Expanded': 'VI',
    'Atomic_Functions_Beyond_Dyadic_Frontiers': 'VI',
    'Rvachev_Atomic_Functions_Report': 'VI',
    'Atomic_Functions_Rvachev_Report_Package': 'VI',
    'Atomic_Functions_Rvachev_Expanded_Report': 'VI',
    'Atomic_Functions_Rvachev_Report_Expanded': 'VI',
    'Atomic_Functions_Rvachev_qBinomial_Frontiers': 'VI',
    'Fabius_Q_Connections_Report': 'VII',
    'Signed_Reciprocal_q_Fabius_Frontiers': 'VII',
    'geometric-sinc-and-exponent-families/Fabius_Rvachev_Frontier_Report': 'VIII',
    'geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier': 'IX',
    'q-fabius-parameter-deformations/fabius_q_frontiers_report': 'X',
    'q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier': 'XI',
    'q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics': 'XII',
}

MARK = 'Absorbed into the consolidated volume'

HEADER = """> **{mark}.**
> This directory is the preserved verification package of a report that is now
> **Part {part}** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/{rel}/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

"""

changed = 0
for dirpath, dirnames, filenames in os.walk(ROOT):
    rel = os.path.relpath(dirpath, ROOT).replace('\\', '/')
    if rel not in PART:
        continue
    for fn in filenames:
        if not re.match(r'^README\.(md|txt)$', fn):
            continue
        p = os.path.join(dirpath, fn)
        t = io.open(p, encoding='utf-8', errors='replace').read()
        if MARK in t:
            continue
        io.open(p, 'w', encoding='utf-8', newline='\n').write(
            HEADER.format(mark=MARK, part=PART[rel], rel=rel) + t)
        changed += 1
        print('  %s  -> Part %s' % (os.path.join(rel, fn), PART[rel]))

print('%d asset READMEs headed' % changed)
missing = [d for d in PART if not os.path.isdir(os.path.join(ROOT, d.replace('/', os.sep)))]
if missing:
    print('WARNING: mapped directories that do not exist: %s' % missing)
