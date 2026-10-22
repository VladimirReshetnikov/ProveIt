"""Owned left-frame diagnostic. Not a Lean/Rocq proof."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import collections, hashlib, json
D=Path(__file__).parent
OLD=D/'deps'
# Only the inspected, previously-owned primitive symbolic transcription is imported.
import sys
sys.path.insert(0,str(OLD))
import model as A
PINS=json.loads((OLD/'INPUT_PINS.json').read_text())
for p,h in PINS.items():
    assert hashlib.sha256((OLD/p).read_bytes()).hexdigest()==h
T=A.table(OLD/'inputs/K215_Formal.tm')
data=json.loads((OLD/'ROUND12_TEMPLATES.json').read_text())
def bounded_scan(l):
    k=0
    for x in l:
        if x[0]=='b':
            k=0 if x[1] else k+1
        elif x[0]=='r':
            _,b,a,c=x
            if b:
                if c:k=0
            else:
                if a:return None
                k+=c
        else:return None
        if k>=8:return None
    return k

def local_step(br,s):
    # Exactly original sstep, except stop before reading the missing frame.
    if s[1] and not s[2]:return None
    try:return A.step(T,br,s)
    except (AssertionError, KeyError):return None

def inspect(k):
    opaque,q,S,op,arg,pos,E,delta,ov,diff=k
    assert opaque
    br=None
    if op=='CD':br=(A.I.PHY[arg],not pos)
    effect=A.X('inc',A.I.PHY[arg]) if op=='CI' else A.X('dec',A.I.PHY[arg]) if op=='CD' and pos else A.X()
    start=(q,False,tuple(A.B(int(b))for b in reversed(S[:-1])),(A.B(int(S[-1])),A.U(0,1,16),A.B(1),A.X()))
    target=tuple(A.B(int(b))for b in E)+(A.U(0,1,16+delta+ov+diff),A.B(1),effect)
    s=start;moved=False;trace=[]
    for i in range(4000):
        q,on,l,r=s
        if q==2 and on:
            counter=bounded_scan(l)
            if counter is not None:
                out=tuple(reversed(l))+r
                if A.norm(out)==A.norm(target):
                    return dict(start=start,pre_home=s,explicit_scan_bound=counter,steps=i,positive_before_home=moved,trace=trace)
                return dict(failed='first admissible Home is not terminal',state=s,scan=counter)
        z=local_step(br,s)
        if z is None:return dict(failed='unframed step required',state=s)
        new,m,kind=z
        trace.append(dict(before=s,after=new,moved=m,kind=kind))
        s=new;moved|=m
    return dict(failed='fuel')
def replay_round12():
    results=[]
    for i,k in enumerate(data['template_keys']):
        if k[0]:
            r=inspect(k);assert 'failed' not in r,(i,k,r)
            results.append(dict(id=i,key=k,**r))
    assert len(results)==76
    out=dict(status='LEFT_FRAME_TERMINAL_HOME_FACTORIZATION_PASS',opaque_templates=len(results),guard_instances=data['opaque_guard_uses'],first_home_is_terminal=True,modified_segments=False,modified_normalizer=False,ordinary_missing_frame_reads=0,steps_max=max(r['steps']for r in results),positive_before_home=collections.Counter(r['positive_before_home']for r in results),boundary_rules='Original sstep only, with onLeft and empty-left rejected. Home is a final composition, not an interpreter transition.',scope='Owned finite replay of 76 template bodies; generic frame-lift and Home contract remain uncompiled.',templates=results)
    (D/'FRAMED_TEMPLATES.json').write_text(json.dumps(out,separators=(',',':')))
    print({k:v for k,v in out.items()if k!='templates'})

if __name__ == "__main__":
    replay_round12()
