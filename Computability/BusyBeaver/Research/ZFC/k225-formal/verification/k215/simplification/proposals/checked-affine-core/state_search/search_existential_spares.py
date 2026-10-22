#!/usr/bin/env python3
"""Concrete screening under a relaxed existential-spare postcondition.

This is explicitly bounded testing, not universal verification. A candidate
must preserve the decoded nine logical registers and continuation, and leave
any legal nonempty spare suffix and nonnegative dispatcher/header gap, at
the first subsequent clean dispatcher frame. Later returns are not accepted.
"""
from pathlib import Path
from search_elimination import parse
import argparse,json,time,hashlib
PHY=(6,2,0,4,3,7,8,5,1)

def frame(pc,regs,spares,gap):
    vals=[0]*9
    for i,j in enumerate(PHY):vals[j]=regs[i]
    one={-1,64+gap}|{i for i,b in enumerate(pc) if b=='1'};p=65+gap
    for v in vals+spares:
        p+=1;one.update(range(p,p+v+1));p+=v+1
    return one

def strip(pc,bit,n):
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            n-=1
            if not n:return pc[:i]
    return ''

def inc(pc):
    return '' if not pc else format((int(pc,2)+1)%(1<<len(pc)),'0'+str(len(pc))+'b')

def expect(site,regs):
    pc,op,a=site;regs=regs.copy()
    if op=='CH':return None
    if op=='CI':regs[a]+=1;pc=inc(pc)
    elif op=='CD' and regs[a]:regs[a]-=1;pc=inc(pc)
    elif op in ('CB','CD'):pc=inc(strip(pc,'0',a if op=='CB' else 1))
    else:pc=strip(pc,'1',a)
    return pc,regs

def decode(h,one):
    if not one or min(one)!=h-1:return None
    right=sorted(x for x in one if x>=h+52)
    if not right or right[0]<h+64:return None
    hd=right[0];last=max(one);p=hd+1;vals=[]
    while p<=last:
        if p in one or p+1 not in one:return None
        start=p+1;p=start
        while p in one:p+=1
        vals.append(p-start-1)
    if p!=last+1 or len(vals)<10:return None
    return {x-h for x in one if h<=x<hd},[vals[j] for j in PHY],vals[9:],hd-h-64

def run(t,site,regs,spares,gap,limit,mutation=None):
    one=frame(site[0],regs,spares,gap);q=83;h=0;used=set();want=expect(site,regs)
    for tick in range(limit+1):
        if tick:
            if q==215:return want is None,tick,used,{'halt':True}
            if q==83:
                got=decode(h,one)
                if got is not None:
                    good=want is not None and got[0]=={i for i,b in enumerate(want[0]) if b=='1'} and got[1]==want[1]
                    return good,tick,used,{'head':h,'pc_one_positions':sorted(got[0]),'registers':got[1],'spares':got[2],'gap':got[3]}
        if tick==limit:break
        used.add(q);b=int(h in one)
        if isinstance(mutation,dict) and (q,b) in mutation:w,d,z=mutation[q,b]
        elif mutation and not isinstance(mutation,dict) and (q,b)==mutation[0]:w,d,z=mutation[1]
        else:w,d,z=t[q,b]
        if b==0 and z==q and ((d>0 and h>max(one)) or (d<0 and h<min(one))):
            return False,tick,used,{'outward_blank_ray':True}
        if w:one.add(h)
        else:one.discard(h)
        q=z;h+=d
    return False,limit,used,{'bound':limit}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('sites');ap.add_argument('--out',default='existential_spare_results.json');ap.add_argument('--limit',type=int,default=20000);ap.add_argument('--max-state',type=int,default=112);ap.add_argument('--only-states');a=ap.parse_args()
    t=parse(a.table);sites=json.loads(Path(a.sites).read_text());states=sorted({q for q,b in t});beg=time.time();short={}
    for site in sites:
        key=tuple(site[1:])
        if key not in short or len(site[0])<len(short[key][0]):short[key]=site
    tests=[]
    for site in short.values():
        for regs,spares,gap in [([0]*9,[0],0),([1]*9,[0,2,1],3),([i%3 for i in range(9)],[2],0)]:
            ok,ticks,used,decoded=run(t,site,regs,spares,gap,a.limit)
            assert ok,('baseline',site,regs,decoded)
            tests.append((site,regs,spares,gap,used))
    attempted=0;surv=[];summary=[];uncovered=[];samplecalls=0
    for q in states:
        if q in (0,83) or q>a.max_state:continue
        if a.only_states and q not in set(map(int,a.only_states.split(','))):continue
        incoming=[(qq,b)for(qq,b),row in t.items()if row[2]==q and qq!=q]
        if len(incoming)!=1:continue
        cases=[x for x in tests if q in x[4]]
        if not cases:uncovered.append(q);continue
        row=incoming[0];before=attempted;hits=0
        for p in states:
            if p==q:continue
            for w in (0,1):
              for d in (-1,1):
                attempted+=1;passed=0
                for site,regs,spares,gap,_ in cases:
                    samplecalls+=1;ok,steps,_,got=run(t,site,regs,spares,gap,a.limit,(row,(w,d,p)))
                    if not ok:break
                    passed+=1
                if ok:
                    hits+=1;surv.append({'removed':q,'incoming':row,'replacement':[w,d,p],'passed_samples':passed})
        summary.append({'state':q,'incoming':row,'covering_samples':len(cases),'attempts':attempted-before,'survivors':hits})
        print('state',q,'attempts',attempted-before,'survivors',hits,'elapsed',round(time.time()-beg,2),flush=True)
    result={'status':'BOUNDED_CONCRETE_SCREEN_ONLY','table_sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(a.sites).read_bytes()).hexdigest(),'sample_count':len(tests),'source_opcode_classes':len(short),'transition_bound':a.limit,'maximum_removed_label':a.max_state,'candidate_count':attempted,'sample_runs':samplecalls,'state_summary':summary,'uncovered_states':uncovered,'survivors':surv,'seconds':time.time()-beg,'postcondition':'At the first subsequent clean dispatcher frame: exact logical registers and decoded continuation; arbitrary nonempty natural spare suffix and any legal nonnegative gap. Later-return existential contracts are not tested. No universal correctness claim.'}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print('DONE',attempted,len(surv),round(time.time()-beg,2))
if __name__=='__main__':main()
