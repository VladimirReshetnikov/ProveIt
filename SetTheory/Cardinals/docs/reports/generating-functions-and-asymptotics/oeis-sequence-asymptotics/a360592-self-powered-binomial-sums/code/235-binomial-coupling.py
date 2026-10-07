"""Exact finite corroboration of the supplementary log-concave coupling lemma.

This module makes no model-specific approximation claim for a higher modulus.
Finite checks are independent of, and do not replace, the proof in the article.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from bisect import bisect_left, bisect_right
from fractions import Fraction
from itertools import combinations
from common import integer, require


def cumulative(weights):
    total = sum(weights, Fraction(0))
    partial = Fraction(0)
    values = []
    for weight in weights:
        partial += weight/total
        values.append(partial)
    return values


def coupling_check(weights, q, offset=0):
    """Check exact index-CDF interlacing and all common quantile cells.

    Supports have 1..41 consecutive integer points; shifts are bounded to
    [-1000,1000] and q to 2..7. Only exact integer/Fraction positive log-concave
    weights are accepted. All comparisons are rational, including rare residues.
    """
    integer(q,2,7,'coupling modulus')
    integer(offset,-1000,1000,'coupling support offset')
    require(isinstance(weights,(list,tuple)) and 1 <= len(weights) <= 41,
            'coupling requires 1 to 41 consecutive weights')
    require(all(isinstance(w,(int,Fraction)) and not isinstance(w,bool) and w > 0 for w in weights),
            'coupling weights must be positive exact integers or fractions')
    weights = [Fraction(w) for w in weights]
    require(all(weights[k]**2 >= weights[k-1]*weights[k+1] for k in range(1,len(weights)-1)),
            'coupling weights must be log concave')
    points = list(range(offset,offset+len(weights)))
    by_residue = {}
    for x,w in zip(points,weights):
        by_residue.setdefault(x%q,[]).append((x,w))
    residues = sorted(by_residue)
    values = {a:[x for x,w in by_residue[a]] for a in residues}
    indices = {a:[(x-a)//q for x in values[a]] for a in residues}
    cdfs = {a:cumulative([w for x,w in by_residue[a]]) for a in residues}
    ordinary = cumulative(weights)
    def cdf_at(a,k):
        index = bisect_right(indices[a],k)-1
        return cdfs[a][index] if index >= 0 else Fraction(0)
    interlacing = 0
    for a,b in combinations(residues,2):
        first = min(indices[a][0],indices[b][0])-1
        last = max(indices[a][-1],indices[b][-1])+1
        for k in range(first,last+1):
            require(cdf_at(a,k) <= cdf_at(b,k) <= cdf_at(a,k+1),
                    'translated index CDF interlacing failed')
            interlacing += 1
    cuts = sorted({Fraction(0),Fraction(1),*ordinary,*[v for a in residues for v in cdfs[a]]})
    probes = [(left+right)/2 for left,right in zip(cuts,cuts[1:])]
    # Lower quantiles are constant on (left,right]; checking the breakpoints
    # too makes the convention at exact CDF values explicit.
    probes += cuts[1:-1]
    max_gap = 0
    for level in probes:
        conditional = [values[a][bisect_left(cdfs[a],level)] for a in residues]
        original = points[bisect_left(ordinary,level)]
        gap = max(conditional)-min(conditional)
        require(gap <= q-1, 'simultaneous quantile gap failed')
        require(all(abs(x-original) <= q-1 for x in conditional),
                'conditional/unconditional common quantile gap failed')
        max_gap = max(max_gap,gap)
    return {'present_residues':residues,'residue_pairs':len(residues)*(len(residues)-1)//2,
            'interlacing_inequalities':interlacing,'quantile_cells':len(cuts)-1,
            'interior_CDF_breakpoints':len(cuts)-2,'max_pair_gap':max_gap}


def coupling_checks():
    cases = pairs = interlacing = cells = breakpoints = 0
    maxima = {str(q):0 for q in range(2,8)}
    boundary = []
    for N in range(21):
        families = [('uniform',[Fraction(1)]*N),
                    ('geometric_1_over_100',[Fraction(1,100)]*N),
                    ('geometric_100',[Fraction(100)]*N),
                    ('decreasing_rational_ratios',[Fraction(2*N+3-k,k+1) for k in range(N)])]
        for q in range(2,8):
            for label,ratios in families:
                weights = [Fraction(1)]
                for ratio in ratios:
                    weights.append(weights[-1]*ratio)
                for offset in (-q-1,-1,0,q-1,2*q+1):
                    result = coupling_check(weights,q,offset)
                    cases += 1; pairs += result['residue_pairs']
                    interlacing += result['interlacing_inequalities']
                    cells += result['quantile_cells']; breakpoints += result['interior_CDF_breakpoints']
                    maxima[str(q)] = max(maxima[str(q)],result['max_pair_gap'])
                    if label == 'uniform' and offset == 0 and N in (0,1,q-1,q,2*q-1,2*q):
                        boundary.append({'N':N,'q':q,'present_residues':result['present_residues'],
                                         'max_pair_gap':result['max_pair_gap']})
    require(cases == 2520, 'coupling fixture case count changed')
    return {'status':'PASS','arithmetic':'exact rational fractions','pmf_modulus_shift_cases':cases,
            'residue_pair_cases':pairs,'index_CDF_interlacing_inequalities':interlacing,
            'common_quantile_cells':cells,'interior_CDF_breakpoints_checked':breakpoints,
            'support_lengths':[1,21],'moduli':[2,3,4,5,6,7],
            'support_offsets_for_each_q':['-q-1','-1','0','q-1','2q+1'],
            'families':['uniform','geometric ratio 1/100','geometric ratio 100','deterministic decreasing rational ratios'],
            'max_pair_gap_by_modulus':maxima,'unshifted_uniform_boundary_cases':boundary,
            'scope':'Supplementary finite log-concave coupling checks; no higher-modulus model approximation or global optimality claim.'}
