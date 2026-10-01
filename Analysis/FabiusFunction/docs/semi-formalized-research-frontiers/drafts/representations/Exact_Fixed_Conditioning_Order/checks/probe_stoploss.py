from pathlib import Path
import json,math
import numpy as np
from probe_masks import tv_mask
rng=np.random.default_rng(301213);count=0;bad=[]
for n in range(2,8):
    for trial in range(300):
        caps=sorted(np.exp(rng.uniform(math.log(.2),math.log(12),n)).tolist(),reverse=True)
        i,j=sorted(rng.choice(n,2,replace=False).tolist());available=[k for k in range(n) if k not in(i,j)]
        common=rng.choice(available,int(rng.integers(0,n-1)),replace=False).tolist()
        e=sorted(common+[i]);l=sorted(common+[j]);cutoff=math.exp(rng.uniform(-3,2))
        te=tv_mask(caps,e,cutoff=cutoff);tl=tv_mask(caps,l,cutoff=cutoff)
        count+=1
        if te-tl < -1e-7:
            r=dict(n=n,caps=caps,cutoff=cutoff,earlier=e,later=l,stoploss_earlier=te,stoploss_later=tl,gap=te-tl)
            bad.append(r);print('COUNTERCANDIDATE',json.dumps(r),flush=True)
            if len(bad)>=5:break
    if len(bad)>=5:break
Path(__file__).with_name('stoploss_probe.json').write_text(json.dumps(dict(cases=count,countercandidates=bad),indent=2)+'\n')
print('DONE',count,'countercandidates',len(bad))
