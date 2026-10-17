#!/usr/bin/env python3
"""Phase-aware folds allowing a decrement of any independently known zero.

The source product invariant is computed from the certified safe root
[6,0,0,0,2,0,0,0,0]. Unlike the earlier guard-only screens, a literal macro
may decrement a different physical register when that register is itself
proved zero by the source phase. Its exact effect is then the identity.
All other existing affine tape/effect checks remain unchanged.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,json,time,hashlib
import rotation_search252 as r
import check_rotation252 as c
from fold_changed252 import read_table

KNOWN_ZERO=set()
EXTRA_ZERO=Counter()
ORIGINAL_ORACLE=c.strict.oracle

def phase_oracle(q,branch,state):
    if q=='43' and state[0]=='mark' and state[1] in KNOWN_ZERO:
        if branch is None or branch[0]!=state[1]:EXTRA_ZERO[state[1]]+=1
        return '3',('plain',None)
    return ORIGINAL_ORACLE(q,branch,state)

def main():
    global KNOWN_ZERO,EXTRA_ZERO
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=r.HERE/'phase-zero-fold-results.json');args=ap.parse_args()
    r.NEWPHYS=(4,5,0,8,6,2,1,7,3);folder=r.HERE/'rotation-candidates';d=json.loads((folder/'mp-cache-permuted252.json').read_text());nodes={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root'];table=read_table(folder/'mp-cache-permuted252.tm');phase=json.loads((r.HERE/'mp-cache-safe-phase.json').read_text());allcases=list(c.cases(nodes,root));excluded={x['case'] for x in phase['excluded']};cases=[];domains={}
    for i,(p,op,arg,z,branch,target) in enumerate(allcases):
        mask=phase['masks'][p]
        if i in excluded:continue
        assert mask is not None
        zeros={r.NEWPHYS[j] for j,a in enumerate(mask) if a==1}
        if op=='CD' and z:zeros.add(r.NEWPHYS[arg])
        if op=='CD' and not z:assert r.NEWPHYS[arg] not in zeros
        cases.append(i);domains[i]=zeros
    c.strict.oracle=phase_oracle
    states=sorted({q for q,b in table},key=int);protected={(str(q),b) for q,b in c.audit.BOX_PAIRS};protected_targets={table[k][2] for k in protected};eligible=[q for q in states if q!='96' and q not in protected_targets and all((q,b)not in protected for b in (0,1))]
    def check(current,i):
        global KNOWN_ZERO,EXTRA_ZERO
        KNOWN_ZERO=domains[i];EXTRA_ZERO=Counter();p,op,arg,z,branch,target=allcases[i]
        try:
            rules,literal=c.strict.run(current,p,branch,target,halt=op=='CH',fuel=1000);assert literal>0
            return sum(rules.values()),None,dict(EXTRA_ZERO)
        except (AssertionError,KeyError) as ex:return 0,str(ex),dict(EXTRA_ZERO)
    # Guard soundness checks: no arbitrary wrong-register decrement is added.
    KNOWN_ZERO=set();assert phase_oracle('43',(0,True),('mark',1)) is None
    KNOWN_ZERO={1};assert phase_oracle('43',(0,True),('mark',1))==('3',('plain',None))
    KNOWN_ZERO={1};assert phase_oracle('43',(0,True),('mark',2)) is None
    usage=defaultdict(list);first=time.monotonic();baseline_extra=0
    for i in cases:
        t=c.Tracking(table);cost,why,extra=check(t,i);assert why is None,(i,why);baseline_extra+=sum(extra.values())
        for q in {q for q,b in t.used}:usage[q].append((cost,i))
    for group in usage.values():group.sort()
    print('BASELINE',len(cases),'extraidentityboxes',baseline_extra,'eligible',len(eligible),flush=True)
    ledger=[];survivors=[];checks=0;extra_attempts=0;reasoncounts=Counter();proved_extra_cases=set()
    for k,dead in enumerate(eligible):
        record={'deleted':int(dead),'failures':[]}
        for target in states:
            if target==dead:continue
            changed={(q,b):(w,d,target if t==dead else t) for(q,b),(w,d,t)in table.items() if q!=dead};assert all(changed[x]==table[x] for x in protected)
            failed=None;why=None;accepted_extra={}
            for _,i in usage[dead]:
                _,why,extra=check(changed,i);checks+=1;extra_attempts+=sum(extra.values())
                if why is not None:failed=i;break
                if extra:accepted_extra[i]=extra;proved_extra_cases.add(i)
            if failed is None:
                accepted_extra={}
                for i in cases:
                    _,why,extra=check(changed,i);checks+=1;extra_attempts+=sum(extra.values())
                    if why is not None:failed=i;break
                    if extra:accepted_extra[i]=extra;proved_extra_cases.add(i)
            if failed is None:
                stem=f'phasezero-delete{dead}-to{target}-251';output=folder/(stem+'.tm');r.save(output,changed);output.write_text(output.read_text().replace('#! start 64\n','#! start 0\n',1));certificate={'deleted':int(dead),'target':int(target),'table':stem+'.tm','cases':len(cases),'independent_zero_cases':accepted_extra,'table_sha256':hashlib.sha256(output.read_bytes()).hexdigest()};survivors.append(certificate);print('SURVIVOR',json.dumps(certificate),flush=True)
            else:reasoncounts[why]+=1
            record['failures'].append([int(target),failed])
        ledger.append(record)
        if k%25==0:print('Progress',k+1,'checks',checks,'extra',extra_attempts,'survivors',len(survivors),'elapsed',round(time.monotonic()-first,2),flush=True)
    result={'source_table':'mp-cache-permuted252.tm','source_sha256':hashlib.sha256((folder/'mp-cache-permuted252.tm').read_bytes()).hexdigest(),'logical_to_physical':r.NEWPHYS,'initial_logical_registers':phase['initial_registers'],'phase_invariant_file':'mp-cache-safe-phase.json','phase_cases':len(cases),'excluded_case_numbers':sorted(excluded),'recipes':len(eligible)*(len(states)-1),'checks':checks,'extra_zero_oracle_uses_in_search':extra_attempts,'accepted_cases_using_extra_zero':sorted(proved_extra_cases),'survivors':survivors,'elapsed_seconds':time.monotonic()-first,'reason_counts':reasoncounts,'ledger':ledger,'scope':'Universal symbolic cases restricted by source-phase masks and named guard. Independently known-zero decrement is the identity. Python implementation not kernel verified; candidate bootstrap must be separately checked.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n');print('DONE',result['recipes'],checks,'survivors',len(survivors),'extrauses',extra_attempts,'elapsed',result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
