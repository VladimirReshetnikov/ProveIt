#!/usr/bin/env python3
"""Finite certificates classifying every blank start of the 252-state body.

Two elementary mathematical lemmas justify the certificate types:
(i) translation preserves a two-way-infinite-tape machine's transition and
    halting behavior;
(ii) a state self-loop moving toward a blank ray runs forever, regardless
     of the symbol it writes behind itself.
No conclusion about the remaining common orbit's halting is drawn.
"""
import argparse
import json
from pathlib import Path
from bootstrap_search import patched


def classify(rows, start, fuel=200):
    q,h,ones = start,0,set()
    for t in range(fuel+1):
        if q==96 and {p-h for p in ones}=={-1,3}:
            return {'initial_state':start, 'kind':'common_configuration',
                    'steps':t,'head':h,'state':q,'ones_relative_to_head':[-1,3]}
        read=int(h in ones)
        if (q,read) not in rows:
            raise AssertionError(('unexpected halting start',start,t))
        w,d,target=rows[q,read]
        virgin = not any(p>=h for p in ones) if d=='R' else not any(p<=h for p in ones)
        if read==0 and target==q and virgin:
            return {'initial_state':start,'kind':'blank_ray_self_loop',
                    'steps':t,'head':h,'state':q,'write':w,'direction':d,
                    'ones_relative_to_head':sorted(p-h for p in ones)}
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
        q=target
    raise AssertionError(('certificate prefix budget exceeded',start))


def main():
    here=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sources',type=Path,default=here/'sources')
    ap.add_argument('--output',type=Path,default=here/'blank_start_certificate.json')
    a=ap.parse_args()
    rows=patched(a.sources/'zfc_254.tm')
    starts=sorted({q for q,b in rows})
    certificates=[classify(rows,q) for q in starts]
    common=[c['initial_state'] for c in certificates if c['kind']=='common_configuration']
    rays=[c['initial_state'] for c in certificates if c['kind']=='blank_ray_self_loop']
    assert len(starts)==252 and len(common)+len(rays)==252
    result={
        'runtime_working_states':len(starts),
        'common_configuration':{'state':96,'head':0,'ones':[-1,3],
                                'all_unlisted_cells':0},
        'starts_reaching_common_configuration':common,
        'starts_provably_entering_blank_ray_self_loop':rays,
        'common_configuration_start_count':len(common),
        'blank_ray_start_count':len(rays),
        'maximum_certificate_prefix_steps':max(c['steps'] for c in certificates),
        'certificates':certificates,
        'scope':'Exact finite-prefix classification plus the elementary blank-ray lemma. The halting status and consistency-search meaning of the common configuration are unresolved; this is not a complete 252-state construction.'
    }
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('certificates','starts_provably_entering_blank_ray_self_loop')},indent=2))


if __name__=='__main__':
    main()
