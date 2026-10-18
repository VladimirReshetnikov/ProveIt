#!/usr/bin/env python3
"""Compile the proposed globally hoisted comparison-success cache transfer.

Dag129's failure jump is lifted from Break1 to Break2; its binary action is
synthesized over every existing full action. All surviving tables must pass
every original strict, phase-unrestricted affine instruction guard.
Source semantics and blank initialization require separate justification.
"""
import json,time,hashlib
from collections import Counter
import rotation_search252 as r
import check_rotation252 as c
from fold_changed252 import read_table

def main():
    r.NEWPHYS=(4,5,0,8,6,2,1,7,3);folder=r.HERE/'rotation-candidates'
    data=json.loads((folder/'mp-cache-permuted252.json').read_text())
    nodes={int(k):tuple(map(tuple,x)) for k,x in data['nodes'].items()}
    assert nodes[197]==(('N',169),('N',172))
    nodes[167]=(nodes[167][0],('B',2))
    nodes[171]=(('N',197),('N',170))
    nodes[186]=(('N',197),('H',))
    nodes[198]=(nodes[198][0],('N',171))
    table=read_table(folder/'mp-cache-permuted252.tm')
    table['252',0]=(0,'R','204')
    table['77',0]=(0,'R','204')
    table['172',1]=(1,'R','252')
    cases=list(c.cases(nodes,data['root']))
    priorities=[i for i,x in enumerate(cases) if x[1:3]==('CB',2)]
    order=priorities+[i for i in range(len(cases)) if i not in priorities]
    states=sorted({q for q,b in table},key=int)+['254']
    ledger=[];survivors=[];checks=0;first=time.monotonic();counts=Counter()
    print('CASES',len(cases),'B2',priorities,flush=True)
    for target in states:
        for write in (0,1):
            for direction in ('L','R'):
                table['120',1]=(write,direction,target);failure=None
                for i in order:
                    p,op,arg,z,branch,goal=cases[i];checks+=1
                    try:
                        rr,literal=c.strict.run(table,p,branch,goal,halt=op=='CH',fuel=1000)
                        assert literal>0
                    except (AssertionError,KeyError) as ex:
                        failure=i;counts[str(ex)]+=1;break
                ledger.append([write,direction,int(target),failure])
                if failure is None:
                    stem=f'hoisted-gate252-{write}{direction}{target}'
                    r.save(folder/(stem+'.tm'),table)
                    (folder/(stem+'.json')).write_text(json.dumps({'nodes':nodes,'root':data['root'],'physical':list(r.NEWPHYS)},indent=2)+'\n')
                    survivor={'action':[write,direction,target],'table':stem+'.tm',
                              'sha256':hashlib.sha256((folder/(stem+'.tm')).read_bytes()).hexdigest(),
                              'graph_states':len(r.gc(table))//2,'cases_passed':len(cases)}
                    survivors.append(survivor);print('SURVIVOR',json.dumps(survivor),flush=True)
    output={'input':'mp-cache-permuted252.tm','cases':len(cases),'break2_cases':priorities,
            'recipes':len(ledger),'checks':checks,'survivors':survivors,'ledger':ledger,
            'failure_counts':counts,'elapsed_seconds':time.monotonic()-first,
            'scope':'Bounded synthesis of one changed B2 action, all original strict affine guards, unchanged four register Box contracts; no phase assumptions, no bootstrap claim.'}
    (r.HERE/'hoisted-gate252-results.json').write_text(json.dumps(output,indent=2)+'\n')
    print('DONE',len(ledger),checks,len(survivors),'elapsed',output['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
