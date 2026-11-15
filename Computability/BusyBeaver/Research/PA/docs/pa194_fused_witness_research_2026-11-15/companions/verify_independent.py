#!/usr/bin/env python3
"""Independent literal-row audit for the two MF compositions.

Imports neither builder nor its helper functions. Checks the local premises,
all quantified finite windows, dense/native bijections, an independently
encoded complete startup frame, and continuing synchronized executions.
The unbounded result is the written induction; finite replay is not that proof.
Python 3.10+ standard library, assertions are deliberately not used.
"""
from pathlib import Path
import argparse, hashlib, itertools, json

def need(test, why):
    if not test: raise ValueError(why)

def parse(path):
    data={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        a,b,c,d,e=line.split();a,b,c,e=map(int,(a,b,c,e))
        need((a,b) not in data and b in (0,1) and c in (0,1) and d in ('L','R'),'malformed transition')
        data[a,b]=(c,-1 if d=='L' else 1,e)
    need(all((q,b) in data for q,_ in data for b in (0,1)),'missing transition')
    return data

def advance(T,c):
    q,h,t=c;t=set(t)
    if q==254:return q,h,t
    w,d,n=T[q,int(h in t)]
    if w:t.add(h)
    else:t.discard(h)
    return n,h+d,t

def image(q):
    if q==51:return 400
    if q==301:return 88
    return q

def incoming(T,n):return [(q,b,w,d)for (q,b),(w,d,r)in sorted(T.items())if r==n]

def history_invariant(q,h,t):
    left=(h-1 in t);right=(h+1 in t)
    if q==101 and left:return False
    if q==11 and left and right:return False
    if q==26 and h in t and (right or h+2 in t):return False
    if q==301 and left:return False
    if q==88 and not left:return False
    return True

def induction_certificate(T):
    # Current guards inspect radius 2. One step shifts the head by at most 1,
    # so radius 3 exhausts every cell on which the conclusion can depend.
    need(history_invariant(74,0,set()),'initial history invariant')
    examined=0;admissible=0
    for q in sorted({q for q,b in T}):
        for mask in range(128):
            t={i-3 for i in range(7)if (mask>>i)&1};examined+=1
            if not history_invariant(q,0,t):continue
            admissible+=1;c=advance(T,(q,0,t))
            need(history_invariant(*c),('inductive history guard',q,mask))
    return {'radius':3,'examined_state_windows':examined,'admissible_state_windows':admissible,'all_successors_satisfy_guards':True}

def static_check(parent,fast,child,dense,labels):
    edits={(26,1):(1,1,91),(101,0):(0,1,17)}
    need(set(parent)==set(fast),'accelerated controls changed')
    need({k:v for k,v in fast.items() if v!=parent[k]}==edits,'wrong acceleration edits')
    need(parent[26,1]==(1,1,42) and parent[42,0]==(0,1,13) and parent[13,0]==(0,-1,91),'first old detour')
    need(parent[101,0]==(0,-1,26) and parent[26,0]==(0,1,194) and parent[194,0]==(0,1,17),'second old detour')
    need(incoming(parent,101)==[(96,0,0,1)],'101 incoming history')
    need(incoming(parent,26)==[(11,0,0,-1),(101,0,0,-1)],'26 incoming history')
    inc11=incoming(parent,11)
    need(inc11 and all(w==0 for q,b,w,d in inc11),'11 incoming writes')
    # History guard for 26/1: the 101 entry writes its eventual head cell zero;
    # a right-moving entry to 11 does the same. Thus only a left-moving entry
    # to 11 can precede a 26/1 step, leaving two zero cells to its right.
    for T in (parent,fast):
        need(incoming(T,101)==[(96,0,0,1)],'101 history after acceleration')
        need(all(q in (11,101) and b==0 and w==0 and d==-1 for q,b,w,d in incoming(T,26)),'26 history after acceleration')
        need(incoming(T,11)==inc11,'11 history after acceleration')
    accel_cases=[]
    for q,b in edits:
        for values in itertools.product((0,1),repeat=5):
            t={i-2 for i,v in enumerate(values)if v}
            if int(0 in t)!=b:continue
            if q==26 and (1 in t or 2 in t):continue
            if q==101 and -1 in t:continue
            c=(q,0,t);reads=[]
            for j in range(3):
                reads.append(c[1]);need(-2<=c[1]<=2,'acceleration exterior read')
                c=advance(parent,c);need(c[0]!=254,'hidden acceleration halt')
            need(c==advance(fast,(q,0,t)),'acceleration finite identity')
            accel_cases.append({'state':q,'window':values,'read_positions':reads})
    need(len(accel_cases)==12,'acceleration case count')
    need(400 not in {q for q,b in fast},'marker label not fresh')
    need(fast[51,0]==(0,1,16) and fast[51,1]==(1,1,51),'marker parent')
    need(fast[301,0]==(0,1,45) and fast[301,1]==(1,1,103),'removed reader')
    need(fast[88,0]==(0,1,122) and fast[88,1]==(1,1,103),'retained reader')
    need(child[51,0]==(0,1,122) and child[51,1]==(1,1,51) and child[88,0]==(0,-1,51),'selector rows')
    ordinary=0
    for (q,b),(w,d,n) in fast.items():
        if q in (301,88):continue
        need(child[image(q),b]==(w,d,image(n)),('ordinary-row mismatch',q,b))
        ordinary+=1
    need(ordinary==384,'ordinary-row count')
    for q,hist in ((301,0),(88,1)):
        edges=incoming(fast,q)
        need(edges and all(w==hist and d==1 for p,b,w,d in edges),'reader history')
        need(q!=74,'initial reader exception')
    fold_cases=[]
    for oldq,hist in ((301,0),(88,1)):
        for bit in (0,1):
            t={i for i,b in ((-1,hist),(0,bit))if b}
            x=advance(fast,(oldq,0,t));goal=(image(x[0]),x[1],x[2]);c=(88,0,t);trace=[]
            for k in range(1,6):
                need(c[1] in (-1,0),'fold exterior read')
                trace.append((c[0],c[1],int(c[1]in c[2])))
                c=advance(child,c);need(c[0]!=254,'hidden fold halt')
                if c==goal:break
            else:raise ValueError('fold failed to close')
            fold_cases.append({'old_state':oldq,'left':hist,'read':bit,'duration':k,'trace':trace})
    need([r['duration']for r in fold_cases]==[5,1,3,1],'fold durations')
    states={q for q,b in child}
    need(len(states)==194 and len(child)==388 and 301 not in states and 51 in states and 400 in states,'child state set')
    need({n for w,d,n in child.values()}-states=={254},'native halt')
    need(len(labels)==195 and labels[0]==74 and labels[-1]==254 and set(labels[:-1])==states and len(set(labels))==195,'label bijection')
    expected={(q,b):(w,d,labels.index(n))for q,native in enumerate(labels[:-1])for b in(0,1)for w,d,n in[child[native,b]]}
    need(dense==expected,'dense/native row conjugacy')
    reach={0};queue=[0]
    for q in queue:
        for b in(0,1):
            n=dense[q,b][2]
            if n!=194 and n not in reach:reach.add(n);queue.append(n)
    need(reach==set(range(194)),'pointed graph reachability')
    return {'history_induction':{'parent':induction_certificate(parent),'accelerated':induction_certificate(fast)},'ordinary_rows':ordinary,'acceleration_cases':accel_cases,'fold_cases':fold_cases,'all_controls_graph_reachable':True}

def make_seed(sites):
    path=sites[25][0];h=-2;gap=48
    tape={h-1,h+gap};tape.update(h+i for i,b in enumerate(path)if b=='1')
    cursor=h+gap+1;registers=[0,0,0,0,0,0,2,0,0]+[1]*26
    for value in registers:
        cursor+=1;tape.update(range(cursor,cursor+value+1));cursor+=value+1
    return (84,h,tape),registers

def continuing_check(parent,fast,child,seed,oldsteps,extra):
    p=f=c=(74,0,set());pc=fc=cc=0;found=None
    startup_counts={'26/1':0,'101/0':0,'301/0':0,'88/0':0}
    later_counts=dict(startup_counts)
    for iteration in range(300000):
        q,h,t=f;bit=int(h in t);edge=(q,bit)
        a=3 if edge in ((26,1),(101,0))else 1
        b=5 if edge==(301,0)else 3 if edge==(88,0)else 1
        counts=startup_counts if found is None else later_counts
        key=f'{q}/{bit}'
        if key in counts:counts[key]+=1
        f=advance(fast,f);fc+=1
        for _ in range(a):p=advance(parent,p);pc+=1
        for _ in range(b):c=advance(child,c);cc+=1
        need(p==f and c==(image(f[0]),f[1],f[2]),('finite synchronization',iteration))
        need(f[0]!=254,'unexpected finite halt')
        if found is None and f==seed:
            need(pc==oldsteps,'parent seed time')
            found={'parent_steps':pc,'fast_steps':fc,'child_steps':cc,'state':c[0],'head':c[1],'one_cells':sorted(c[2]),'counts':dict(startup_counts),'complete_tape_equality':True}
        if found is not None and fc==found['fast_steps']+extra:break
    need(found is not None and fc==found['fast_steps']+extra,'replay cap')
    need(later_counts['26/1']>0 and later_counts['301/0']>0,'both transformations must recur after startup')
    return {'startup':found,'additional_fast_steps':extra,'after_startup_uses':later_counts,'final_clocks':{'parent':pc,'fast':fc,'child':cc}}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--extra',type=int,default=10000);a=ap.parse_args()
    root=a.root.resolve();reports=[]
    for spec in json.loads((root/'inputs/specifications.json').read_text()):
        inp=root/'inputs'/spec['parent'];d=root/'machines'/spec['name']
        pb=(inp/'machine.native.tm').read_bytes();need(hashlib.sha256(pb).hexdigest()==spec['parent_native_sha256'],'parent hash')
        parent=parse(inp/'machine.native.tm');fast=parse(d/'accelerated_parent.native.tm');child=parse(d/'machine.native.tm');dense=parse(d/'machine.tm');labels=json.loads((d/'labels.json').read_text())
        static=static_check(parent,fast,child,dense,labels)
        sites=json.loads((inp/'sites.json').read_text());seed,registers=make_seed(sites);record=json.loads((inp/'startup.json').read_text())
        need(seed==(record['state'],record['head'],set(record['one_cells'])),'independent seed layout')
        runs=continuing_check(parent,fast,child,seed,record['steps'],a.extra)
        reports.append({'name':spec['name'],'status':'PASS','parent_sha256':spec['parent_native_sha256'],'dense_sha256':hashlib.sha256((d/'machine.tm').read_bytes()).hexdigest(),'states':194,'rows':388,'register_seed':registers,'static':static,'finite_replay':runs})
    out={'status':'PASS','builder_imported':False,'reports':reports,'proof_scope':'Exact finite literal certificates supporting the written uniform local simulation. This executable replay is not a kernel proof of PA calibration or a proof by extrapolation.'}
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
