"""Check first-use bounds, exact coalescence gaps, and the weaving recurrence."""
import json
import random
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from twistkh import Run
from twistkh.core import _geometry
from twistkh.preflight import basis_size,degree_profile,generator_basis_bound

rng=random.Random(20261008)
checked=0
for trial in range(100):
    b=rng.randrange(2,6)
    runs=[Run(rng.randrange(1,b),rng.choice((-1,1))*rng.randrange(1,5)) for _ in range(rng.randrange(1,8))]
    for support in range(1<<len(runs)):
        s=support.bit_count();d=len({r.generator for j,r in enumerate(runs) if support&(1<<j)})
        c=len(_geometry(b,runs,support).circles)
        assert c<=b+s-2*d and (b+s-2*d-c)%2==0
        checked+=1
merges=[]
for trial in range(100):
    b=rng.randrange(2,5)
    prefix=[Run(rng.randrange(1,b),rng.randrange(1,4)) for _ in range(2)]
    suffix=[Run(rng.randrange(1,b),-rng.randrange(1,4)) for _ in range(2)]
    i=rng.randrange(1,b);a=rng.randrange(1,6);z=rng.randrange(1,6);sign=rng.choice((-1,1))
    di=basis_size(b,prefix+suffix)['exact_basis']
    de=basis_size(b,prefix+[Run(i,1)]+suffix)['exact_basis']-di
    before=basis_size(b,prefix+[Run(i,a),Run(i,sign*z)]+suffix)['exact_basis']
    e=a+sign*z
    after=basis_size(b,prefix+([Run(i,e)] if e else [])+suffix)['exact_basis']
    gap=(a+z+2*a*z-abs(e))*de
    assert before-after==gap
    merges.append({'strands':b,'a':a,'b':z,'relative_sign':sign,'gap':gap})
weaving=[]
a,z=2,7
for r in range(1,51):
    runs=[Run(1,1),Run(2,-1)]*r
    value=basis_size(3,runs)
    assert value['exact_basis']==z+2
    if r<=12:
        profile=degree_profile(3,runs)
        assert profile['exact_basis']==z+2
    weaving.append({'r':r,'crossings':2*r,'basis':z+2,'peak_matchings':value['peak_matchings'],
                    'generator_bound':generator_basis_bound(3,runs)})
    a,z=z,7*z-9*a
out={'seed':20261008,'first_use_circle_checks':checked,'coalescence_context_checks':len(merges),
     'weaving_recurrence_checks':len(weaving),'failures':0,'merges':merges,'weaving':weaving}
Path('results/cost_certificates.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ('merges','weaving')})
