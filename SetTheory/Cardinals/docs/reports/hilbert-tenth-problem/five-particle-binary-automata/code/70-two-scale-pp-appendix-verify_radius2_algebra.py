"""Independent orientation-reversed exact enumeration and collision check.
Reads inert certificate JSON; does not import or run the producer.
"""
import itertools,json
from pathlib import Path
words=list(itertools.product((0,1),repeat=5))
ends=list(itertools.product((0,1),repeat=4))
complete=set()
for bits in itertools.product((0,1),repeat=15):
    base={q+(0,):v for q,v in zip(ends,(0,)+bits)}
    table=[]
    for w in words:
        v=w[-1]
        for k in range(1,5):
            v+=base[w[k-1:4]+(0,)*k]-base[w[k:5]+(0,)*k]
        if v not in (0,1):break
        table.append(str(v))
    if len(table)==32:complete.add(''.join(table))
assert len(complete)==428
cert=json.load(open(Path(__file__).with_name('radius2_certificate.json')))
projections={''.join(str(w[k]) for w in words) for k in range(5)}
certified=set()
for item in cert['certificates']:
    table=item['table']; L=item['period']
    assert table in complete and item['a']!=item['b']
    def output(v):
        x=[int(a) for a in format(v,'0'+str(L)+'b')]
        y=[]
        for j in range(L):
            local=''.join(str(x[k%L]) for k in range(j-2,j+3))
            y.append(table[int(local,2)])
        return int(''.join(y),2)
    assert output(item['a'])==output(item['b'])==item['image']
    certified.add(table)
assert len(certified)==423 and certified.isdisjoint(projections)
assert certified|projections==complete
print('Independent reversed conservation identity: 428 tables; 423 explicit collisions checked; exactly five projections remain.')
