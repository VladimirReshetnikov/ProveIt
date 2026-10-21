#!/usr/bin/env python3
"""Independent valid-frame counterexample to naive 52/154 helper borrowing.

The trial has 214 working states and passes its four intended three-transition
selector blocks.  It does NOT preserve the CB1 primitive at source ordinal
4724.  This refutes that uniform source-to-machine contract only; no claim is
made about this trial's blank-run consistency equivalence.

The finite-frame convention follows the credited ProveIt runtime interface.
This checker imports no symbolic runtime, allocator, or search implementation.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
BASE_SHA='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
TRIAL_SHA='fa3cbf23de9e8078df61d6c1c16d071719344e8d641e04db27d435b372f63d7e'
SOURCE_SHA='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
def need(p,msg):
    if not p:raise ValueError(msg)
def table(path):
    out={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        need((q,b)not in out and b in(0,1)and w in(0,1)and d in('L','R'),'invalid table')
        out[q,b]=(w,1 if d=='R'else-1,t)
    need(len(out)==2*len({q for q,b in out}),'incomplete table')
    return out

def frame(pc):
    # Nine zero-valued primary registers, one zero spare, gap zero.
    ones={-1,64}|{i for i,b in enumerate(pc)if b=='1'}
    ones.update(range(66,85,2))
    return ones

def clean(q,h,ones):
    if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
    right=sorted(x for x in ones if x>=h+52)
    if not right or right[0]<h+64:return False
    pos,last,values=right[0]+1,max(ones),[]
    while pos<last:
        if pos in ones or pos+1 not in ones:return False
        a=pos+1;pos=a
        while pos in ones:pos+=1
        values.append(pos-a-1)
    return pos==last+1 and len(values)>=10

def run(T,initial):
    q,h,ones=84,0,set(initial);trace=[]
    for tick in range(10000):
        if tick and(clean(q,h,ones)or(q,int(h in ones))not in T):
            return {'state':q,'head':h,'ones':sorted(ones),'steps':tick,'clean_dispatch':clean(q,h,ones),'trace':trace}
        b=int(h in ones);w,d,z=T[q,b];trace.append([q,h,b,w,d,z])
        if w:ones.add(h)
        else:ones.discard(h)
        q,h=z,h+d
    raise ValueError('finite replay bound exhausted; no conclusion')

def verify():
    paths=[ROOT/'inputs/primary.tm',ROOT/'research/REJECTED-52-154-214.native.tm',ROOT/'inputs/sites215.json']
    for p,h in zip(paths,[BASE_SHA,TRIAL_SHA,SOURCE_SHA]):need(hashlib.sha256(p.read_bytes()).hexdigest()==h,'input hash')
    T,N=map(table,paths[:2]);sites=json.loads(paths[2].read_text());need(sites[4724]==['11011','CB',1],'source ordinal')
    expected={(q,b):(w,d,52 if t==154 else t)for(q,b),(w,d,t)in T.items()if q!=154}
    expected[52,0]=(0,-1,211);expected[52,1]=(1,-1,117);expected[117,1]=(1,1,176)
    need(N==expected and len(N)==428,'exact 214-state trial recipe')
    incoming=lambda z:[(q,b,w,d)for(q,b),(w,d,t)in T.items()if t==z]
    need(all(w==1 and d==1 for q,b,w,d in incoming(52)),'old52 predecessor marker')
    need(all(w==0 and d==1 for q,b,w,d in incoming(154)),'old154 predecessor marker')
    blocks=[]
    for old,m in((52,1),(154,0)):
        for b in(0,1):
            local={-1:m,0:b};before=dict(local);q,h=52,0;trace=[]
            for _ in range(3):
                need(h in local,'local block inspected exterior')
                read=local[h];w,d,z=N[q,read];trace.append([q,h,read,w,d,z]);local[h]=w;q,h=z,h+d
            goal=T[old,b][2];goal=52 if goal==154 else goal
            need((q,h,local)==(goal,1,before),'selector block mismatch')
            blocks.append({'old_state':old,'marker':m,'bit':b,'trace':trace,'target':goal})
    initial=frame('11011');old,new=run(T,initial),run(N,initial)
    # CB1 cuts before the rightmost zero: 11011 -> 11; increment wraps,
    # shifting the address origin one cell left. Header/register cells stay.
    expected_ones=[-2,64,66,68,70,72,74,76,78,80,82,84]
    need((old['state'],old['head'],old['ones'],old['steps'])==(84,-1,expected_ones,163),'parent result')
    need(new['clean_dispatch']and(new['state'],new['head'],new['steps'])==(84,0,588),'trial result')
    need(new['ones']==[-1,0,1,3,4,8,64,66,68,70,72,74,76,78,80,82,84],'trial tape')
    record={'status':'CONCRETE_UNIFORM_RUNTIME_COUNTEREXAMPLE','scope':__doc__,'parent_sha256':BASE_SHA,'trial_sha256':TRIAL_SHA,'source_sha256':SOURCE_SHA,
       'source_ordinal':4724,'site':sites[4724],'registers':[0]*9,'spares':[0],'gap':0,
       'initial':{'state':84,'head':0,'ones':sorted(initial)},'old52_incoming':incoming(52),'old154_incoming':incoming(154),
       'four_intended_selector_blocks':blocks,'parent':old,'trial':new,'working_states':214,'transition_rows':428}
    return record

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);a=ap.parse_args();r=verify()
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:r[k]for k in('status','source_ordinal','site','working_states','transition_rows')}|{'parent_steps':r['parent']['steps'],'trial_steps':r['trial']['steps'],'parent_head':r['parent']['head'],'trial_head':r['trial']['head']},indent=2))
if __name__=='__main__':main()
