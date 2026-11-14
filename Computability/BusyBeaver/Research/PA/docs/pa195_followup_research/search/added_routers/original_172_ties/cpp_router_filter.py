"""Subprocess bridge to the C++ router matching filter."""
import json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent

def install(r):
    def calculate(raw,shape,desired_states=194,helpers=1):
        states=sorted({q for q,_ in raw});shape=sorted(shape)
        lines=[f'{len(states)} {len(shape)} {helpers} {desired_states}']
        for q in states:
            w0,d0,n0=raw[q,0];w1,d1,n1=raw[q,1]
            lines.append(f'{q} {w0} {int(d0)} {n0} {w1} {int(d1)} {n1}')
        lines.append(' '.join(map(str,shape)))
        text='\n'.join(lines)+'\n'
        result=subprocess.run([str(HERE/'router_filter')],input=text,text=True,stdout=subprocess.PIPE,check=True)
        d=json.loads(result.stdout);groups=d.pop('groups');hits=d.pop('hits')
        out={k:d[k] for k in ('best_optimistic','router_signatures','signature_groups','target_folds','distinct_extra_edge_sets')}
        if helpers==1:
            out['hits']=[(tuple(router),d['target_folds'])for i,j in hits for router in groups[i]]
        else:
            out['hits']=[([tuple(x)for x in groups[i]],[tuple(x)for x in groups[j]],d['target_folds'])for i,j in hits]
        return out
    r.one_router_candidates=lambda raw,shape,desired_states=194:calculate(raw,shape,desired_states,1)
    r.two_router_candidates=lambda raw,shape,desired_states=194:calculate(raw,shape,desired_states,2)
