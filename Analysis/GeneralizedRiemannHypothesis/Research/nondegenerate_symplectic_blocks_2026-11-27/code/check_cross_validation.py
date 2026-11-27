#!/usr/bin/env python3
"""Compare independent exhaustive matrix enumeration with exact moment laws."""
import json
from fractions import Fraction as F
from pathlib import Path
from exact_laws import distributions

root=Path(__file__).resolve().parents[1]
cases=json.loads((root/'results/exhaustive.json').read_text())['cases']
checks=0
def frac(v):
    return F(v['numerator'],v['denominator'])
for case in cases:
    q,n=case['q'],case['block_dimension_N']
    law=distributions(n,q,joint=True)
    for actual,key in [('full_matrix_total_variation','full_tv'),('rank_total_variation','rank_tv'),('alpha','alpha')]:
        assert frac(case[actual])==law[key],(q,n,actual)
        checks+=1
    for row in case['rank_distribution']:
        a=n-row['rank']
        assert frac(row['iid_probability'])==law['uniform_nullity'][a]
        assert frac(row['model_probability'])==law['block_nullity'][a]
        checks+=2
    for row in case['defect_distribution']:
        k=row['half_nullity']
        assert frac(row['iid_probability'])==law['iid_defect_nullity'][2*k]
        assert frac(row['model_probability'])==law['iid_defect_nullity'][2*k]*law['likelihood'][k]
        checks+=2
out={'status':'passed','independent_parameter_cases':len(cases),'exact_comparisons':checks,
     'methods':['exhaustive finite-field Gram fibre enumeration','Gaussian kernel moments and rational inversion']}
(root/'results/cross_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
