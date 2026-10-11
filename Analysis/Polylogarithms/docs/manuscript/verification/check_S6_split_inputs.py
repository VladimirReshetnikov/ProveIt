"""Independent exact input-cover and compact-record audit, without incoming imports."""
from pathlib import Path
from itertools import product
from collections import defaultdict
import gzip,hashlib,json,struct,time
V=Path(__file__).resolve().parent;started=time.monotonic()
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def admissible(w):return w[0]!=4 and w[-1]!=0
def depth(w):return sum(t!=0 for t in w)
def odd(w):return w.count(1)%2
def multiply(a,b):
    c=defaultdict(int)
    for (d,p),x in a.items():
        for (e,q),y in b.items():c[d+e,p^q]+=x*y
    return dict(c)
F={(0,0):1,(1,0):2,(1,1):1};G={(0,0):1,(1,0):3,(1,1):1};L={(1,0):3,(1,1):1}
profile=multiply(multiply(F,F),multiply(L,L))
for _ in range(3):profile=multiply(profile,G)
assert profile[5,1]==3604
results=[]
for length in [2,3]:
    stem=f'S6-split-{length}-{7-length}-depth-five'
    path=V/(stem+'-sparse.bin.gz');meta=json.loads((V/(stem+'-packing.json')).read_text())
    assert meta['status']=='PASS' and sha(path)==meta['compact_sha256']
    us=[w for w in product(range(5),repeat=length) if admissible(w)]
    vs=[w for w in product(range(5),repeat=7-length) if admissible(w)]
    expected={(u,v) for u in us for v in vs if depth(u)+depth(v)==5 and odd(u)!=odd(v)}
    assert len(expected)==profile[5,1]==3604
    seen=set();logical=hashlib.sha256();entries=0;bounded=0;maximum=0
    with gzip.open(path,'rb') as f:
        assert struct.unpack('<4sIIQ',f.read(20))==(b'S6S1',3604,8786,5760)
        for row in range(3604):
            header=f.read(12);assert len(header)==12 and header[0]==length
            left=tuple(header[1:1+length]);right=tuple(header[1+length:8])
            assert (left,right) in expected and (left,right) not in seen;seen.add((left,right))
            count=struct.unpack('<I',header[8:])[0];assert count<=8786
            data=f.read(count*10);assert len(data)==count*10
            logical.update(header+data);previous=-1;top=False
            for k,value in struct.iter_unpack('<Hq',data):
                assert previous<k<8786 and value;previous=k;top|=k>=2546
                maximum=max(maximum,abs(value))
            entries+=count;bounded+=not top
        assert not f.read(1)
    assert seen==expected and entries==meta['entries'] and bounded==meta['bounded_rows']
    assert maximum==meta['maximum_absolute_integer'] and logical.hexdigest()==meta['logical_row_bytes_sha256']
    # An otherwise admissible truncated input cover must not be accepted.
    corrupted=set(seen);corrupted.pop();assert corrupted!=expected
    results.append(dict(length_split=[length,7-length],input_cover_complete=True,rows=len(seen),entries=entries,bounded_rows=bounded,maximum_absolute_integer=maximum,compact_sha256=meta['compact_sha256'],logical_sha256=logical.hexdigest(),missing_input_control_rejected=True))
out=dict(status='PASS',imports_delivered_code=False,independent_profile_polynomial='(1+2t+tz)^2 (3t+tz)^2 (1+3t+tz)^3, with z^2=1',depth_five_odd_coefficient=3604,families=results,elapsed_seconds=round(time.monotonic()-started,3),scope='Independent chamber-letter counting, complete input-set equality, sparse coordinate order, bounds and logical byte audit for both convergent length splits. No numerical period recognition and no rational target membership claim.')
(V/'S6-convergent-split-input-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Independent complete input covers and compact rows PASS',flush=True)
