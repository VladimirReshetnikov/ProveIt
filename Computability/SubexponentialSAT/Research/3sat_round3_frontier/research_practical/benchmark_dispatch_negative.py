"""Deliberately adverse root-filter profile: verifies selective dispatch matters."""
import json,random,statistics,time
from packet_extraction import Ring,centered_half_gray,projective_odd_root,adaptive_homogeneous,direct_coefficient
rng=random.Random(202610270221)
ring=Ring(64,(1,1));root=(0,1);beta=[1]*8
rows=[[tuple(rng.getrandbits(64) for _ in range(2)) for _ in beta] for _ in range(8)]
methods={'half':lambda stats=None:centered_half_gray(rows,beta,ring,stats),
         'cube_unselected':lambda stats=None:projective_odd_root(rows,beta,ring,root,3,stats),
         'adaptive':lambda stats=None:adaptive_homogeneous(rows,beta,ring,root,stats)}
expected=direct_coefficient(rows,beta,ring)
results={}
for name,fn in methods.items():
    stats={}
    if fn(stats)!=expected:raise AssertionError('warmup mismatch')
    secs=[]
    for _ in range(3):
        start=time.perf_counter();value=fn();secs.append(time.perf_counter()-start)
        if value!=expected:raise AssertionError('timed mismatch')
    results[name]={'stats':stats,'seconds':secs,'median_seconds':statistics.median(secs)}
if results['adaptive']['stats']['method']!='centered_half_gray':raise AssertionError('wrong dispatch')
print(json.dumps({'status':'PASS','case':'eight ones, e2 ell1 p64','results':results,'cube_slowdown':results['cube_unselected']['median_seconds']/results['half']['median_seconds']},indent=2))
