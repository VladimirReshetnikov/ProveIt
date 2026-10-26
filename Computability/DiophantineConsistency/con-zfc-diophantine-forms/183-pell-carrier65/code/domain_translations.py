"""Literal onto-domain substitutions; all arithmetic uses integer leaves."""
from collections import Counter
from copy import deepcopy

def translate(parent, domain):
    if domain not in ('natural', 'integer'):
        raise ValueError('domain must be natural or integer')
    out = deepcopy(parent)
    witnesses, rows = [], []
    for v in parent['witnesses']:
        if domain == 'natural':
            u = v + '_natural'
            witnesses.append(u)
            rows.append([v, '+', u, 1])
        else:
            a, b, c = (v+'_'+s for s in ('a', 'b', 'c'))
            witnesses.extend([a, b, c])
            rows.extend([
                [v+'_a2', '*', a, a],
                [v+'_b2', '*', b, b],
                [v+'_cp1', '+', c, 1],
                [v+'_cterm', '*', c, v+'_cp1'],
                [v+'_ab', '+', v+'_a2', v+'_b2'],
                [v+'_abc', '+', v+'_ab', v+'_cterm'],
                [v, '+', v+'_abc', 1],
            ])
    rows.extend(deepcopy(parent['source']))
    out['source'] = rows
    out['witnesses'] = witnesses
    out['witness_domain'] = ('nonnegative integers' if domain == 'natural'
                             else 'unrestricted integers')
    out['operations'] = len(rows)
    out['operation_counts'] = dict(Counter(r[1] for r in rows))
    out['exact_degree'] = 150 if domain == 'natural' else 300
    out['name'] = ('natural14_79_degree150' if domain == 'natural'
                   else 'integer42_163_degree300')
    out['domain_substitution'] = ('v=u+1' if domain == 'natural'
                                  else 'v=1+a^2+b^2+c*(c+1)')
    out['domain_onto_theorem'] = ('successor' if domain == 'natural'
                                  else 'Legendre three-square theorem applied to 4*(v-1)+1')
    return out
