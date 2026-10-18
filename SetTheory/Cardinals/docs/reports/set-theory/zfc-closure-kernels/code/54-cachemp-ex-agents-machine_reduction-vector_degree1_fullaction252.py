#!/usr/bin/env python3
"""Complete single-incoming-edge full-action deletion sweep for cache-MP252.

Uses the phase-aware exact-vector, valid-spare-suffix checker in
vector_effect_fold252. All 55 original Box support rows and their targets
remain fixed. Each incoming row may write either bit, move either direction,
and target any remaining state or halt. Fuel is 1,000 affine rules per guard.
"""
from collections import defaultdict,Counter
import json,time,hashlib
import vector_effect_fold252 as v

r,c=v.r,v.c

def main():
    r.NEWPHYS=(4,5,0,8,6,2,1,7,3)
    folder=r.HERE/'rotation-candidates'
    d=json.loads((folder/'mp-cache-permuted252.json').read_text())
    nodes={int(k):tuple(map(tuple,x)) for k,x in d['nodes'].items()}
    table=v.read_table(folder/'mp-cache-permuted252.tm')
    phase=json.loads((r.HERE/'mp-cache-safe-phase.json').read_text())
    allcases=list(c.cases(nodes,d['root']))
    excluded={x['case'] for x in phase['excluded']}
    cases=[i for i in range(len(allcases)) if i not in excluded]
    c.strict.oracle=v.oracle;c.strict.canon=v.canon
    states=sorted({q for q,b in table},key=int)
    protected={(str(q),b) for q,b in c.audit.BOX_PAIRS}
    protected_targets={table[k][2] for k in protected}
    eligible=[q for q in states if q!='96' and q not in protected_targets
              and all((q,b) not in protected for b in (0,1))]
    incoming={q:[k for k,val in table.items() if val[2]==q and k[0]!=q]
              for q in eligible}
    eligible=[q for q in eligible if len(incoming[q])==1]
    assert len(eligible)==131

    def check(current,i):
        p,op,arg,z,branch,target=allcases[i]
        v.establish_domain(phase['masks'][p],op,arg,z)
        actualtarget=v.project_canonical(target)
        v.OPS=Counter();v.LAST_SPARES=0
        try:
            rules,literal=c.strict.run(current,p,branch,actualtarget,
                                       halt=op=='CH',fuel=1000)
            assert literal>0
            return sum(rules.values()),None
        except (AssertionError,KeyError) as ex:return 0,str(ex)

    first=time.monotonic();usage=defaultdict(list)
    for i in cases:
        traced=c.Tracking(table);cost,why=check(traced,i)
        assert why is None,(i,why)
        for q in {q for q,b in traced.used}:usage[q].append((cost,i))
    for group in usage.values():group.sort()
    print('BASELINE',len(cases),'eligible',len(eligible),flush=True)
    recipes=checks=0;ledger=[];survivors=[];reasoncounts=Counter()
    for number,dead in enumerate(eligible):
        row=incoming[dead][0]
        record={'deleted':int(dead),'incoming':row,'failures':[]}
        changed={key:val for key,val in table.items() if key[0]!=dead}
        for target in [q for q in states if q!=dead]+['254']:
            for write in (0,1):
                for direction in ('L','R'):
                    changed[row]=(write,direction,target);recipes+=1
                    assert all(changed[key]==table[key] for key in protected)
                    failure=None
                    for _,i in usage[dead]:
                        _,why=check(changed,i);checks+=1
                        if why is not None:failure=i;break
                    if failure is None:
                        for i in cases:
                            _,why=check(changed,i);checks+=1
                            if why is not None:failure=i;break
                    if failure is None:
                        stem=f'vector-fullaction-delete{dead}-{write}{direction}{target}-251'
                        out=folder/(stem+'.tm');r.save(out,changed)
                        out.write_text(out.read_text().replace('#! start 64\n','#! start 0\n',1))
                        certificate={'deleted':dead,'incoming':row,
                                     'action':[write,direction,target],
                                     'table':stem+'.tm','cases':len(cases),
                                     'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}
                        survivors.append(certificate)
                        print('SURVIVOR',json.dumps(certificate),flush=True)
                    else:reasoncounts[why]+=1
                    record['failures'].append([int(target),write,direction,failure])
        ledger.append(record)
        if number%10==0:
            print('Progress',number+1,'recipes',recipes,'checks',checks,
                  'survivors',len(survivors),'elapsed',round(time.monotonic()-first,2),flush=True)
    assert recipes==132048
    result={'source_table':'mp-cache-permuted252.tm',
            'source_sha256':hashlib.sha256((folder/'mp-cache-permuted252.tm').read_bytes()).hexdigest(),
            'logical_to_physical':list(r.NEWPHYS),
            'phase_cases':len(cases),'excluded_case_numbers':sorted(excluded),
            'eligible_deletions':len(eligible),'recipes':recipes,'checks':checks,
            'survivors':survivors,'elapsed_seconds':time.monotonic()-first,
            'reason_counts':reasoncounts,'ledger':ledger,
            'scope':'Complete one-incoming-edge full-action family with unchanged Box support. Phase domain from certified safe root, exact symbolic primary vectors, arbitrary finite valid spare suffix relation, 1000 affine-rule fuel. A rejection is not a semantic impossibility proof; no kernel certificate.'}
    (r.HERE/'vector-degree1-fullaction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',recipes,checks,'survivors',len(survivors),'elapsed',result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
