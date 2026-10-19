#!/usr/bin/env python3
"""Independent bit-mask verification of the 240-state positive-block proof."""
from pathlib import Path
import argparse, hashlib, json, sys
from collections import Counter
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Enabled assertions are required')
P=Path(__file__).resolve().parents[1]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(p):
    t={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R')
        t[q,b]=(w,1 if d=='R' else -1,z)
    return t

def inv(q,h,x):
    def bit(k):
        assert -2<=k<=2, ('guard outside proof footprint',q,k)
        return (x>>(k+2))&1
    if q in (55,90,142): return bit(h-1)==1
    if q==72: return bit(h-2)==1 and bit(h-1)==0
    return True

def move(t,q,h,x):
    assert -2<=h<=2, ('read outside proof footprint',q,h)
    w,d,z=t[q,(x>>(h+2))&1]
    return z,h+d,(x&~(1<<(h+2)))|(w<<(h+2))
def phi(q): return 72 if q==90 else q

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=P/'evidence/local_root.json');a=ap.parse_args()
    oldpath=P/'reference/rotated241_old.tm';newpath=P/'machines/zfc240_old.tm'
    assert sha(oldpath)=='88a1f42b01b7e2b4bf29bc1b3819b78f1e7a17cefaefbc003654f2f5cc202c2f'
    assert sha(newpath)=='547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'
    old,new=parse(oldpath),parse(newpath);qs={q for q,b in old};ns={q for q,b in new}
    assert len(qs)==241 and len(ns)==240 and ns==qs-{90}
    assert set(old)=={(q,b)for q in qs for b in (0,1)}
    assert set(new)=={(q,b)for q in ns for b in (0,1)}
    assert {r for w,d,r in new.values()}-ns=={254}
    changes={k:v for k,v in new.items()if old[k]!=v}
    assert changes=={(72,0):(0,-1,144),(72,1):(1,-1,36),(79,1):(1,1,72)}
    incoming={q:sorted((s,b,w,d)for(s,b),(w,d,r)in old.items()if r==q)for q in (55,142,72,90)}
    assert incoming=={55:[(37,1,1,1)],142:[(119,1,1,1)],72:[(55,0,0,1),(142,0,0,1)],90:[(79,1,1,1)]}
    hist=Counter();count=0
    for q in sorted(qs):
        for x in range(32):
            if not inv(q,0,x): continue
            r,h,y=move(old,q,0,x);assert inv(r,h,y)
            expected=(phi(r),h,y)
            length=9 if q==72 and ((x>>2)&1)==0 else 3 if q in (72,90) else 1
            z,k,v=phi(q),0,x
            for _ in range(length):
                assert z!=254
                z,k,v=move(new,z,k,v)
            assert (z,k,v)==expected,(q,x,length,expected,(z,k,v))
            hist[length]+=1;count+=1
    assert count==7640 and dict(hist)=={1:7616,9:4,3:20}
    assert all(inv(95,0,x)for x in range(32))
    order=[95]+sorted(ns-{95});ren={q:i for i,q in enumerate(order)}|{254:240}
    canonical=parse(P/'machines/zfc240.tm')
    assert canonical=={(ren[q],b):(w,d,ren[r])for(q,b),(w,d,r)in new.items()}
    assert sha(P/'machines/zfc240.tm')=='508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd'
    out={'status':'ROOT_INDEPENDENT_LOCAL_ALL_TAPE_PASS','old_sha256':sha(oldpath),'new_sha256':sha(newpath),
         'canonical_sha256':sha(P/'machines/zfc240.tm'),'proof_checker_sha256':sha(Path(__file__)),
         'invariant_implications':count,'positive_whole_tape_blocks':count,'duration_histogram':dict(sorted(hist.items())),
         'state_map':'90 to 72; all other states fixed','invariant':'55,142,90 have left1;72 has lefttwo10',
         'read_write_guard_window':[-2,2],'outside_tape':'arbitrary and unchanged; infinite support permitted',
         'global_induction':'Invariant starts at95, is preserved by every old step, and matched new blocks have positive lengths1,3,9 and contain no premature halt.',
         'clock':'t_new=t_old+8V(72,0)+2[V(72,1)+V(90,0)+V(90,1)]',
         'canonical_start':0,'canonical_dispatcher':84,'canonical_halt':240,'working_states':240,'rows':480}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
