"""Independent full integer certificate audit, using finite differences.
Unlike the production certificate checker, this reconstructs quadratic gaps from
values at 0,1,2 and derives primitive Newton factors from binomial coefficients.
It also verifies every archived member against the supplied expanded files.
"""
from pathlib import Path
from math import comb, gcd
from collections import Counter
import csv, hashlib, json, zipfile
BASE=Path('/workspace/shared/preorder-gamma-degree4')
OUT=Path(__file__).resolve().parent
archive=BASE/'degree4_certificates.zip'
archive_count=0
with zipfile.ZipFile(archive) as z:
    for entry in z.infolist():
        if entry.is_dir(): continue
        name=Path(entry.filename).name
        data=z.read(entry)
        assert (BASE/name).read_bytes()==data, name
        archive_count+=1
seen=set(); previous=None
stats=Counter(); minima=[None]*3; minima_degree4=[None]*3
min_disc=None; quadratic_counts=Counter(); equality_counts=Counter()
with (BASE/'pendant10_coefficients.csv').open() as f:
    reader=csv.reader(f)
    assert next(reader)==['a0','a1','a2','a3','a4','b0','b1','b2','b3']
    for cells in reader:
        row=tuple(map(int,cells)); assert len(row)==9
        assert row not in seen
        assert previous is None or previous<row
        seen.add(row); previous=row
        a=row[:5]; b=row[5:]
        assert a[0]==b[0]==1 and b[3]>0
        assert all(x>=0 for x in row)
        assert all(a[k]>=b[k] for k in range(4))
        assert all(a[k]>0 and b[k]>0 for k in range(4))
        degree=4 if a[4] else 3
        stats[f'core_degree_{degree}_pairs']+=1
        for k in range(1,4):
            left=comb(4,k-1)*comb(4,k+1)
            right=comb(4,k)**2
            d=gcd(left,right); left//=d; right//=d
            values=[]
            for m in range(4):
                gamma=[1]+[a[i]+m*b[i-1] for i in range(1,5)]
                values.append(left*gamma[k]**2-right*gamma[k-1]*gamma[k+1])
            C=values[0]
            second=values[2]-2*values[1]+values[0]
            assert second%2==0
            A=second//2; B=values[1]-C-A
            assert values[3]==C+3*B+9*A
            assert A>=0 and C>=0
            if B<0:
                disc=4*A*C-B*B
                assert disc>=0
                stats['negative_linear_instances']+=1
                min_disc=disc if min_disc is None else min(min_disc,disc)
                if disc==0: equality_counts[f'inequality_{k}_negative_linear_discriminant_zero']+=1
            quadratic_counts[(k,C,B,A)]+=1
            if C==0: equality_counts[f'inequality_{k}_constant_zero']+=1
            minima[k-1]=C if minima[k-1] is None else min(minima[k-1],C)
            if degree==4:
                minima_degree4[k-1]=C if minima_degree4[k-1] is None else min(minima_degree4[k-1],C)
            stats['verified_quadratic_instances']+=1
        stats['distinct_coefficient_pairs']+=1
assert stats['distinct_coefficient_pairs']==412622
assert stats['verified_quadratic_instances']==1237866
assert stats['negative_linear_instances']==180706
assert min_disc==0
report=dict(stats)
report.update(status='PASS',archive_members_bytewise_verified=archive_count,
    genuinely_distinct_indexed_quadratics=len(quadratic_counts),
    minimum_constant_gaps=minima,minimum_constant_gaps_actual_degree_four=minima_degree4,
    minimum_discriminant_when_B_negative=min_disc,equality_counts=dict(equality_counts),
    csv_sha256=hashlib.sha256((BASE/'pendant10_coefficients.csv').read_bytes()).hexdigest(),
    archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest())
(OUT/'certificate_audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2,sort_keys=True))
