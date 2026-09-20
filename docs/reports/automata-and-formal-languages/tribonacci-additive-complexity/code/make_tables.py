#!/usr/bin/env python3
"""Create the article's tables from the certified data (standard library)."""
import csv
from decimal import Decimal, getcontext
import json
from pathlib import Path
from tribonacci import ROOT, load_automaton, prefix_counts, tribonacci_numbers

getcontext().prec=80
beta=Decimal('1.84')
for _ in range(30):
    beta -= (beta**3-beta**2-beta-1)/(3*beta**2-2*beta-1)
densities={3:(21*beta**2-38*beta+5)/22,
           4:(-55*beta**2+72*beta+67)/22,
           5:(17*beta**2-17*beta-25)/11}
M=load_automaton()
L=json.load(open(ROOT/'data/eigenvector.json'))
rows=[]
for i in range(38):
    entries=[]
    for q in (i,i+38):
        entries += [str(q)]+[r'--' if t<0 else str(t) for t in M['transitions'][q]]+[str(M['outputs'][q])]
    rows.append(' & '.join(entries)+r' \\')
(ROOT/'tables/transitions_rows.tex').write_text('\n'.join(rows)+'\n')
nonzero=[(q,*row)for q,row in enumerate(L['coefficients']) if any(row)]
rows=[]
for i in range(33):
    rows.append(' & '.join(str(a) for row in (nonzero[i],nonzero[i+33]) for a in row)+r' \\')
(ROOT/'tables/eigenvector_rows.tex').write_text('\n'.join(rows)+'\n')
Ns=[10**3,10**6,10**9,10**12,10**18,10**30,10**100]
all_counts=[]
for N in Ns:
    c=prefix_counts(N,M)
    all_counts.append({'N':str(N),'counts':{str(k):str(v)for k,v in c.items()}})
(ROOT/'data/large_prefix_counts.json').write_text(json.dumps(all_counts,indent=2)+'\n')
with (ROOT/'data/prefix_counts.csv').open('w',newline='') as out:
    writer=csv.writer(out);writer.writerow(['N','a=1','a=3','a=4','a=5'])
    for item in all_counts:
        writer.writerow([item['N']]+[item['counts'][str(k)]for k in (1,3,4,5)])
rows=[]
for N in Ns[:4]:
    c=prefix_counts(N,M)
    exponent=len(str(N))-1
    rows.append('$10^{'+str(exponent)+'}$ & '+' & '.join(f'{c[k]:,}'.replace(',','{,}') for k in (3,4,5))+r' \\')
(ROOT/'tables/counts_rows.tex').write_text('\n'.join(rows)+'\n')
T=tribonacci_numbers(61)
with (ROOT/'data/tribonacci_cutoff_counts.csv').open('w',newline='') as out:
    writer=csv.writer(out);writer.writerow(['k','T_k','a=1','a=3','a=4','a=5'])
    for k,t in enumerate(T):
        c=prefix_counts(t,M);writer.writerow([k,t]+[c[j]for j in (1,3,4,5)])
results={'beta':str(beta),'densities':{str(k):str(v)for k,v in densities.items()},
         'error_exponent':str((Decimal(7)/5).ln()/beta.ln()),
         'mean':str((13*beta**2+4*beta+33)/22)}
(ROOT/'data/constants.json').write_text(json.dumps(results,indent=2)+'\n')
# Numerator rows, coefficient arrays are more compact and less error prone than long formulae.
gfs=json.load(open(ROOT/'data/generating_functions.json'))
rows=[]
for i in range(31):
    values=[gfs[str(j)]['numerator'][i] if i<len(gfs[str(j)]['numerator']) else 0 for j in (3,4,5)]
    rows.append(' & '.join(map(str,[i]+values))+r' \\')
(ROOT/'tables/numerator_rows.tex').write_text('\n'.join(rows)+'\n')
print(json.dumps(results,indent=2))
