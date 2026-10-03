"""Export the 24 unsymmetrized rank-four mixed-cover templates.

A table term [i,j,k,m] contributes
m * product_S binom(left_population[S], left_quotas[i][S])
  * product_T binom(right_population[T], right_quotas[j][T])
to the coefficient of t**k. Type order is increasing nonzero neighbor mask.
"""
from pathlib import Path
import json
from support_kernels import bipartite_kernel_table

out = {'format': 'binomial-product support kernel, version 1',
       'note': 'These are exact support formulas, not positivity certificates '
               'for all rank-four Newton gaps.', 'templates': []}
for a, b in [(1, 3), (2, 2)]:
    for core in range(1 << (a*b)):
        ql, qr, terms = bipartite_kernel_table(a, b, core)
        out['templates'].append({'left_cover': a, 'right_cover': b,
          'core_mask': core, 'left_quotas': ql, 'right_quotas': qr,
          'terms_i_j_degree_multiplicity': terms})
path = Path(__file__).resolve().parents[1]/'data'/'rank4_templates.json'
path.write_text(json.dumps(out, separators=(',', ':'))+'\n')
print(f'Exported {len(out["templates"])} exact templates to {path.name}.')
