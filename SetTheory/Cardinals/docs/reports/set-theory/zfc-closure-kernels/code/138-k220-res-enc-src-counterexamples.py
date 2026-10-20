#!/usr/bin/env python3
"""Replay two exact finite counterexamples to tempting 220-state patches.

Frame conventions and the expected source primitive are adapted from the
pinned K221 independent_runtime.py, retaining its mathematical scope.  The
simulator below uses native state labels and no runtime proof module.
"""
import csv,json,hashlib
from pathlib import Path
import context as c

PHY=(6,2,0,4,3,7,8,5,1)

def frame(pc,logical,spares,gap=0):
    physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    ones={-1,64+gap}|{i for i,b in enumerate(pc)if b=='1'}
    pos=65+gap
    for value in physical+list(spares):
        pos+=1;ones.update(range(pos,pos+value+1));pos+=value+1
    return ones

def inc(pc):
    if not pc:return '',1
    n=len(pc);v=int(pc,2)+1
    return format(v%(1<<n),'0'+str(n)+'b'),int(v==1<<n)

def strip(pc,bit,n):
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            n-=1
            if n==0:return pc[:i]
    return ''

def expected(site,logical,spares):
    pc,op,arg=site;logical=list(logical);spares=list(spares);gap=0;shift=0
    if op=='CI':logical[arg]+=1;spares.append(1);pc,shift=inc(pc)
    elif op=='CD' and logical[arg]:logical[arg]-=1;gap=1;pc,shift=inc(pc)
    elif op in('CD','CB'):pc,shift=inc(strip(pc,'0',1 if op=='CD'else arg))
    elif op=='CC':pc=strip(pc,'1',arg)
    else:raise ValueError('Counterexample uses a nonhalting primitive')
    return 84,-shift,{x-shift for x in frame(pc,logical,spares,gap+shift)}

def dispatch(q,h,ones):
    if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
    right=sorted(x for x in ones if x>=h+52)
    if not right or right[0]<h+64:return False
    p=right[0]+1;last=max(ones);values=[]
    while p<last:
        if p in ones or p+1 not in ones:return False
        start=p+1;p=start
        while p in ones:p+=1
        values.append(p-start-1)
    return p==last+1 and len(values)>=10

def run(table,ones,q=84,limit=100000):
    ones=set(ones);h=0;trace=[]
    for tick in range(limit+1):
        # This ray condition is itself an exact proof of subsequent divergence.
        ray=(q,0)in table and table[q,0][1:]==(1,q)and h>max(ones,default=-1)
        if tick and(dispatch(q,h,ones)or q==254 or ray):
            return(q,h,ones),trace,'right_blank_ray'if ray else'dispatch'if q==84 else'halt'
        if tick==limit:return(q,h,ones),trace,'limit'
        bit=int(h in ones);write,move,target=table[q,bit]
        trace.append((tick,q,h,bit,write,move,target))
        if write:ones.add(h)
        else:ones.discard(h)
        q=target;h+=move

def conf(x):return {'state':x[0],'head':x[1],'one_cells':sorted(x[2])}

def write_trace(path,rows):
    with path.open('w',newline='')as f:
        w=csv.writer(f);w.writerow(['tick','state','head','read','write','move','target']);w.writerows(rows)
    return {'file':path.name,'rows':len(rows),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def main():
    out=c.OUT/'counterexamples';out.mkdir(exist_ok=True)
    report={'status':'TWO_REJECTED_PATCHES_REPLAYED','baseline_table_sha256':c.EXPECTED_TABLE,'cases':[]}
    cases=[('drop50',40,{k:(w,d,75 if q==50 else q)for k,(w,d,q)in c.T.items()if k[0]!=50}),
           ('drop198',0,{k:v for k,v in c.T.items()if k[0]!=198})]
    cases[1][2][66,0]=(1,-1,113)
    for name,index,table in cases:
        site=c.ROWS[index];logical=[0]*9;spares=[1]
        initial=frame(site[0],logical,spares);want=expected(site,logical,spares)
        old,oldtrace,oldstop=run(c.T,initial)
        actual,trace,stop=run(table,initial)
        assert old==want and oldstop=='dispatch'
        assert actual!=want and stop!='limit'
        rec={'name':name,'status':'FALSIFIED','source_ordinal':index,'site':site,
             'logical_registers':logical,'spares':spares,'extra_gap':0,
             'working_states':len(table)//2,'initial_one_cells':sorted(initial),
             'baseline_steps':len(oldtrace),'baseline_matches_expected':True,
             'mutant_stop':stop,'mutant_steps':len(trace),'actual':conf(actual),'expected':conf(want),
             'mutant_trace':write_trace(out/f'{name}.csv',trace),
             'baseline_trace':write_trace(out/f'{name}_baseline.csv',oldtrace),
             'scope':'Concrete valid source-interface frame; no claim that this frame occurs on the blank run.'}
        if stop=='right_blank_ray':rec['divergence_certificate']={'state':actual[0],'head':actual[1],
            'rightmost_one':max(actual[2]),'zero_row':table[actual[0],0],
            'reason':'Head is strictly right of every one; the zero row moves right and retains the same state. Its written cell is left behind.'}
        report['cases'].append(rec)
        print(name,stop,len(trace),'baseline',len(oldtrace),flush=True)
    # Stronger initialized-machine negative control for the second patch.
    blank,trace,stop=run(cases[1][2],set(),q=0,limit=1000000)
    assert stop=='right_blank_ray'
    report['drop198_blank_divergence']={'status':'EXACT_RIGHT_RAY_DIVERGENCE',
        'steps_to_ray':len(trace),'state':blank[0],'head':blank[1],
        'rightmost_one':max(blank[2],default=-1),'zero_row':cases[1][2][blank[0],0],
        'trace':write_trace(out/'drop198_blank.csv',trace),
        'reason':'From the recorded point the head sees a fresh zero forever; the transition moves right in the same working state.'}
    print('drop198 blank',stop,len(trace),blank[0],blank[1],flush=True)
    (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
