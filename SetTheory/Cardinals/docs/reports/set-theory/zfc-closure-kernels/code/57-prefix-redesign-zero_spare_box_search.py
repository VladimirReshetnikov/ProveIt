#!/usr/bin/env python3
"""Literal box contractions specialized to an all-zero spare suffix.

This finite search does not prove a box theorem. Every survivor is also screened
against the full changed MP0 source tree, conditionally on its proposed renamed
box interfaces. The new MP0 initializer supplies 93 zero spare blocks, so the
stronger invariant is meaningful; the old arbitrary-spare search could reject
a correct specialization. Positive results still require unbounded box proofs
and a new literal blank-start certificate.
"""
from __future__ import annotations
from collections import Counter
import hashlib, json, sys, time
from pathlib import Path
import mp_protocol_runtime as m
import permutation252_spare_fold_search as box

HERE=Path(__file__).resolve().parent
PERM=(0,2,6,8,7,5,3,1,4)

def samples():
    vectors=[[0]*9,[1]*9,[2]*9,[i%3 for i in range(9)],
             [(8-i)%3 for i in range(9)],[0,0,5,0,0,0,1,0,2],
             [4,0,0,0,0,0,0,0,0]]
    for op in ('mark','inc','dec0','decp'):
        for r in range(9):
            for vector in vectors:
                for count in (0,1,2,7,93):
                    values=vector.copy()
                    if op=='dec0':values[r]=0
                    if op=='decp':values[r]=max(1,values[r])
                    mark=sum(v+2 for v in values[:r])+1
                    raw=box.paint(values+[0]*count)
                    if op!='mark':raw[mark]=0
                    wanted=values.copy()
                    if op=='inc':wanted[r]+=1
                    if op=='decp':wanted[r]-=1
                    prefix=box.paint(wanted)
                    if op=='mark':prefix[mark]=0
                    start=m.audit.SKIP[r] if op=='mark' else 73 if op=='inc' else 43
                    stop=(2 if r==0 else 6) if op=='mark' else 48 if op=='inc' else 3 if op=='dec0' else (63 if r==0 else 48)
                    left={-1,-4,-7}
                    yield dict(op=op,register=r,values=values,spare_count=count,
                               start=start,stop=stop,left=left,
                               ones=left|{i for i,b in enumerate(raw) if b},prefix=prefix)

def run(table,case,fuel,dead=None,keep=None):
    relocate=lambda q:keep if q==dead else q
    q,h,ones=relocate(case['start']),0,case['ones'].copy()
    used=set()
    for step in range(fuel):
        if q==254:return False,'halt',used,step
        row=q,int(h in ones);used.add(row)
        if row not in table:return False,'missing_row',used,step
        w,d,q=table[row]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
        if h>=0:continue
        if h!=-1 or q!=relocate(case['stop']):return False,'first_exit_state',used,step+1
        if {i for i in ones if i<0}!=case['left']:return False,'left_context',used,step+1
        prefix=case['prefix']
        if any(int(i in ones)!=b for i,b in enumerate(prefix)):return False,'primary_registers',used,step+1
        end=max(ones);cursor=len(prefix)
        while cursor<=end:
            if cursor in ones or cursor+1 not in ones or cursor+2 in ones:
                return False,'zero_spare_shape',used,step+1
            cursor+=2
        return True,None,used,step+1
    return False,'fuel',used,fuel

def mutate(table,dead,keep,mode):
    candidate={k:(w,d,keep if t==dead else t) for k,(w,d,t) in table.items() if k[0]!=dead}
    if mode>=0:
        w,d,t=table[dead,mode]
        candidate[keep,mode]=w,d,keep if t==dead else t
    assert len(candidate)==502
    return candidate

def main():
    begun=time.monotonic();fuel=5000
    table=m.audit.read_table((HERE.parent/'bootstrap/mp_rebased252.tm').read_bytes())
    cases=list(samples());usage=[];costs=[]
    for i,c in enumerate(cases):
        ok,reason,used,cost=run(table,c,fuel)
        assert ok,('baseline',i,reason)
        usage.append(used);costs.append(cost)
    protected=(m.audit.BOX_STATES|{table[k][2] for k in m.audit.BOX_PAIRS})-{96}
    states=sorted({q for q,b in table})
    recipes=[]
    for dead in sorted(protected):
        for keep in states:
            if keep in (dead,96):continue
            recipes.append((dead,keep,-1))
            if keep in protected and dead>keep:continue
            for bit in (0,1):
                if table[dead,bit]!=table[keep,bit]:recipes.append((dead,keep,bit))
    result=dict(scope=__doc__,table_sha256=hashlib.sha256((HERE.parent/'bootstrap/mp_rebased252.tm').read_bytes()).hexdigest(),
                fuel=fuel,baseline_samples=len(cases),recipes=len(recipes),
                failures=[],literal_survivors=[],checks=0)
    preferred=sorted(range(len(cases)),key=costs.__getitem__)
    print('Baseline',len(cases),'passed;',len(recipes),'recipes.',flush=True)
    for n,(dead,keep,mode) in enumerate(recipes):
        candidate=mutate(table,dead,keep,mode)
        touched={(dead,0),(dead,1)}|({(keep,mode)} if mode>=0 else set())
        affected=[i for i in preferred if usage[i]&touched]
        affectedset=set(affected)
        order=affected+[i for i in preferred if i not in affectedset]
        for i in order:
            ok,reason,used,cost=run(candidate,cases[i],fuel,dead,keep);result['checks']+=1
            if not ok:
                result['failures'].append([dead,keep,mode,i,reason,cost]);break
        else:result['literal_survivors'].append([dead,keep,mode])
        if (n+1)%3000==0:print('Checked',n+1,'survivors',len(result['literal_survivors']),'seconds',round(time.monotonic()-begun,2),flush=True)
    result['sample_seconds']=time.monotonic()-begun
    result['failure_reasons']=dict(Counter(x[4] for x in result['failures']))
    (HERE/'zero_spare_box_results.json').write_text(json.dumps(result,indent=2)+'\n')
    m.generate();m.audit.PERM=PERM
    stringtable={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()}
    guards=m.guards();assert m.certify(stringtable,guards)['passed']
    oldoracle=m.a.strict.oracle
    result['conditional_affine']=[]
    for dead,keep,mode in result['literal_survivors']:
        def relocated(q,branch,state):
            qs=[q]+([str(dead)] if q==str(keep) else [])
            answers=[]
            for qq in qs:
                answer=oldoracle(qq,branch,state)
                if answer is not None:
                    exit_state,effect=answer
                    answers.append((str(keep) if exit_state==str(dead) else exit_state,effect))
            if not answers:return None
            assert all(a==answers[0] for a in answers),('incompatible proposed interfaces',q,state,answers)
            return answers[0]
        m.a.strict.oracle=relocated
        candidate=mutate(table,dead,keep,mode)
        check=m.certify({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in candidate.items()},guards)
        result['conditional_affine'].append(dict(dead=dead,keep=keep,mode=mode,check=check))
        if check['passed']:
            print('CONDITIONAL SURVIVOR',dead,keep,mode,flush=True)
            data=m.audit.encode(candidate)
            (HERE/f'zero-spare-{dead}-{keep}-{mode}.tm').write_bytes(data)
    m.a.strict.oracle=oldoracle
    result['total_seconds']=time.monotonic()-begun
    (HERE/'zero_spare_box_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('failures','conditional_affine','literal_survivors','scope')},indent=2),flush=True)
    print('Literal survivors',len(result['literal_survivors']),'conditional survivors',sum(x['check']['passed'] for x in result['conditional_affine']),flush=True)

if __name__=='__main__':main()
