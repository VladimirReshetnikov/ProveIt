#!/usr/bin/env python3
from pathlib import Path
import csv
import json
from fractions import Fraction
from math import prod
from factorial_divisibility import A,B,Ratio,certificate,height_one_denominators,primes_upto

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT/'data'


def main():
    cases=[]
    configurations=[('A',A,(2,),7),('A',A,(3,),1),('A',A,(5,),1),
                    ('A',A,(2,3,5),42),('B',B,(1,),385),('B',B,(2,),5),
                    ('B',B,(3,),1),('B',B,(1,2,3),770)]
    for name,r,ks,expected in configurations:
        cutoff=max([r.maximum]+[abs(k-j) for k in ks for j in ks])
        cs=[certificate(r,ks,p) for p in primes_upto(cutoff)]
        optimal=prod(c['prime']**max(0,-c['minimum']) for c in cs)
        assert optimal==expected
        cases.append({'name':name,'numerator':list(r.numerator),'denominator':list(r.denominator),
                      'slopes':list(ks),'cutoff':cutoff,'optimal_multiplier':optimal,'certificates':cs})
    obj={'format_version':1,'method':'Closed weighted digit graphs with exact integer potentials',
         'cases':cases}
    (DATA/'certificates.json').write_text(json.dumps(obj,indent=2)+'\n')
    with (DATA/'sharp_constants.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['ratio','slopes','optimal_multiplier','prime','minimum_valuation','witness_n','states','edges'])
        for case in cases:
            for c in case['certificates']:
                w.writerow([case['name'],';'.join(map(str,case['slopes'])),case['optimal_multiplier'],
                            c['prime'],c['minimum'],c['witness'],len(c['states']),c['edge_count']])
    # Compact all-prime minima table, typeset in the article.
    lines=[]
    for case in cases:
        mins={c['prime']:c['minimum'] for c in case['certificates']}
        label=case['name']+' / '+''.join('(%dn+1)'%k for k in case['slopes'])
        cells=[f'${label}$']+[str(mins.get(p,0)) for p in [2,3,5,7,11,13,17,19,23,29]]+[str(case['optimal_multiplier'])]
        lines.append(' & '.join(cells)+r' \\')
    (DATA/'minima_table.tex').write_text('\n'.join(lines)+'\n')
    with (DATA/'sequence_U.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','U_n'])
        for n in range(51):
            u=42*A.value(n)/((2*n+1)*(3*n+1)*(5*n+1))
            assert u.denominator==1
            w.writerow([n,u.numerator])
    source=json.loads((DATA/'sporadic_parameters.json').read_text())
    assert len(source['parameters'])==52
    table=[]
    with (DATA/'atlas_52.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['index','numerator_parameters','denominator_parameters','positive_offset_denominators','negative_offset_denominators'])
        for i,(top,bot) in enumerate(source['parameters'],1):
            r=Ratio(tuple(top),tuple(bot));assert r.integral() and r.height==1
            pos,neg=height_one_denominators(r)
            w.writerow([i,';'.join(map(str,top)),';'.join(map(str,bot)),';'.join(map(str,pos)),';'.join(map(str,neg))])
            fs=lambda xs: r'$'+','.join(map(str,xs))+'$'
            table.append(' & '.join([str(i),fs(top),fs(bot),fs(pos),fs(neg)])+r' \\')
    (DATA/'atlas_table.tex').write_text('\n'.join(table)+'\n')
    statistics={'cases':len(cases),'certificates':sum(len(c['certificates']) for c in cases),
                'states':sum(len(z['states']) for c in cases for z in c['certificates']),
                'transitions':sum(z['edge_count'] for c in cases for z in c['certificates'])}
    (DATA/'certificate_statistics.json').write_text(json.dumps(statistics,indent=2)+'\n')
    print(json.dumps(statistics,indent=2))

if __name__=='__main__':main()
