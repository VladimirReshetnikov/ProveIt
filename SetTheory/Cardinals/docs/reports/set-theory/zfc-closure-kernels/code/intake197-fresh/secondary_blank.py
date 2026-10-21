"""Own independent sparse replay of both presentations of the secondary216."""
from pathlib import Path
import argparse,gzip,json
ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();p=a.packet
def table(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R')
        t[q,b]=(w,1 if d=='R' else -1,z)
    return t
T=table(p/'secondary/k216-120.native.tm');C=table(p/'secondary/k216-120.tm')
Q={q for q,b in T};m={q:i for i,q in enumerate(sorted(Q))};m[254]=216
assert len(Q)==216 and len(T)==432 and set(T)=={(q,b) for q in Q for b in (0,1)}
assert {z for w,d,z in T.values()}-Q=={254} and m[0]==0
assert {(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in T.items()}==C
st=json.loads(gzip.decompress((p/'secondary/startup.json.gz').read_bytes()))
assert st['steps']==len(st['trace'])==96244
logical=[4,0,0,0,0,0,0,0,0];physical=[0]*9
for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=logical[i]
expected={-9,57};pos=58
for v in physical+[1]*40:
    expected.update(range(pos+1,pos+v+2));pos+=v+2
for name,t in [('native',T),('canonical',C)]:
    q,h,ones=0,0,set()
    for event in st['trace']:
        b=int(h in ones);w,d,z=t[q,b]
        wanted=event if name=='native' else [m[event[0]],event[1],event[2],event[3],event[4],m[event[5]]]
        assert [q,h,b,w,d,z]==wanted
        if w:ones.add(h)
        else:ones.discard(h)
        q,h=z,h+d
    assert q==(84 if name=='native' else m[84]) and h==-8 and ones==expected
assert st['state']==84 and st['head']==-8 and st['gap']==1 and st['registers']==logical and st['spares']==[1]*40 and st['one_cells']==sorted(expected)
out=dict(status='INDEPENDENT_SECONDARY_NATIVE_CANONICAL_BLANK_PASS',steps=96244,working_states=216,rows=432,native_dispatch=84,canonical_dispatch=m[84],head=-8,gap=1,registers=logical,spares=40,one_cells=sorted(expected),complete_trace_compared=True,scope='Exact finite blank replay and direct whole-tape frame; no runtime or calibration claim.')
a.output.write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
