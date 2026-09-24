#!/usr/bin/env python3
"""Additional exact checks of generating-function data and periodic consequences.

This supplements, and does not replace, the all-level induction certificate.
Uses the Python standard library only.
"""
from pathlib import Path
from fractions import Fraction
import json
from rs_maximum import maximum,autocorrelation
from verify import require,template_matrices

ROOT=Path(__file__).resolve().parents[1]

def main():
    data=ROOT/'data'
    obj=json.loads((data/'generating_function.json').read_text())
    require(obj['denominator_ascending']==[1,1,-2,-4], 'denominator mismatch')
    num=obj['numerator_ascending']
    require(len(num)==43 and num[-1]==-7589872, 'numerator degree mismatch')
    peaks=[0]+[maximum(m).value for m in range(1,501)]
    for m in range(501):
        coefficient=sum(q*peaks[m-j] for j,q in enumerate(obj['denominator_ascending'])
                        if m>=j)
        require(coefficient==(num[m] if m<len(num) else 0),
                f'generating-function mismatch at {m}')
    b=[1,1,5]
    for _ in range(3,501):b.append(-b[-1]+2*b[-2]+4*b[-3])
    corrections={str(m):peaks[m]-b[m-2] for m in range(2,501)
                 if peaks[m]!=b[m-2]}
    require(corrections==obj['correction_terms'], 'correction table mismatch')
    require(peaks[40:43]==obj['peak_initial_m40_42'], 'initial values mismatch')
    raw=json.loads((data/'template_matrices.json').read_text())
    printed=[tuple(tuple(Fraction(x) for x in row) for row in a) for a in raw['L']]
    require(printed==template_matrices(), 'mirrored template matrices mismatch')
    for row in json.loads((data/'direct_scan.json').read_text()):
        result=maximum(row['m'])
        require(result.value==row['max'] and list(result.shifts)==row['shifts'],
                'exploratory array scan disagrees')
    count=0
    for m in range(3,10):
        length=1<<m
        signs=[(-1)**bin(j & (j>>1)).count('1') for j in range(length)]
        correlations=[]
        for k in range(1,length):
            direct=sum(signs[j]*signs[(j+k)%length] for j in range(length))
            require(direct==autocorrelation(m,k)+autocorrelation(m,length-k),
                    'periodic defining sum mismatch')
            correlations.append(direct)
            count+=1
        if m>=5:
            previous=maximum(m-2)
            shifts=[k for k,c in enumerate(correlations,1)
                    if abs(c)==max(map(abs,correlations))]
            expected=[(1<<(m-1))-previous.shifts[0],(1<<(m-1))+previous.shifts[0]]
            require(shifts==expected,'periodic maximizing locations mismatch')
            require(max(map(abs,correlations))==4*previous.value,'periodic peak mismatch')
    summary=dict(status='PASS',generating_function_levels=500,
                 mirrored_template_matrices=13,exploratory_array_levels=[2,26],
                 periodic_defining_sum_checks=count)
    (data/'auxiliary_checks.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
