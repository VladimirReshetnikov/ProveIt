#!/usr/bin/env python3
"""New independent replay for the pinned comparison and rejected 207-state witness.
No external source modules, downloaded code, network or assertions are used.
A success result does not certify a below-208 machine or any consistency claim.
"""
from pathlib import Path
from collections import deque
import hashlib, json, sys, argparse
R=Path(__file__).resolve().parent

def need(c,m):
    if not c: raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads((R/p).read_text())
def table(p):
    t={}
    for l in (R/p).read_text().splitlines():
        if not l.strip() or l.lstrip().startswith('#'):continue
        a=l.split();need(len(a)==5,'row arity '+p)
        q,b,w,d,z=a;q,b,w,z=map(int,(q,b,w,z))
        need((q,b) not in t,'duplicate '+p);need(b in (0,1) and w in (0,1) and d in ('L','R'),'alphabet '+p)
        t[q,b]=(w,d,z)
    states={q for q,b in t};need(set(t)=={(q,b) for q in states for b in (0,1)},'totality '+p)
    return t

def canonical(t):
    states={q for q,b in t};halt=set(z for w,d,z in t.values())-states;need(halt=={254},'native halt')
    nums={0:0,254:-1};queue=deque([0]);rows=[]
    while queue:
        q=queue.popleft()
        for b in (0,1):
            w,d,z=t[q,b]
            if z not in nums:nums[z]=len(nums)-1;queue.append(z)
            rows.append((nums[q],b,w,d,nums[z]))
    need(set(nums)==states|halt,'graph unreachable')
    return hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),nums

def steps(t,q,h,ones,n):
    ones=set(ones);trace=[]
    for k in range(n):
        b=int(h in ones);need((q,b) in t,'premature halt');w,d,z=t[q,b]
        trace.append([k,q,h,b,w,1 if d=='R' else -1,z])
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1;q=z
    return {'steps':n,'state':q,'head':h,'ones':sorted(ones)},trace

def decode_frame(q,h,ones,sites):
    ones=set(ones)
    if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return None
    pc='';maxdepth=max(map(len,sites))
    for k in range(maxdepth+1):
        if pc in sites:break
        if k==maxdepth:return None
        pc+='1' if h+k in ones else '0'
    right=sorted(x for x in ones if x>=h+44)
    if not right or right[0]<h+56:return None
    header=right[0]
    if any(x in ones for x in range(h+len(pc),header)):return None
    p=header+1;last=max(ones);vals=[]
    while p<last:
        if p in ones or p+1 not in ones:return None
        st=p+1;p=st
        while p in ones:p+=1
        vals.append(p-st-1)
    if p!=last+1 or len(vals)<10:return None
    return {'stored_PC':pc.rstrip('0'),'resolved_leaf_address':pc,'resolved_ordinal':sites[pc][0],'resolved_operation':sites[pc][1],'header':header-h,'logical_registers':[vals[j] for j in (6,2,0,4,3,7,8,5,1)],'spares':vals[9:]}

def frame(pc,regs,spares):
    physical=[0]*9
    for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=regs[i]
    ones={-1,56}|{i for i,b in enumerate(pc) if b=='1'};p=57
    for n in physical+spares:
        p+=1;ones.update(range(p,p+n+1));p+=n+1
    return ones

def replay(negative_controls=False):
    idx=load('evidence/input_index.json');need(len(idx)==9,'input count')
    groups={};tabs={};starts={}
    for x in idx:
        p=x['path'];d=x['dense_path'];s=x['source_path']
        need(sha(R/p)==x['native_sha256'],'native hash');need(sha(R/d)==x['dense_sha256'],'dense hash');need(sha(R/s)==x['source_sha256'],'source hash')
        t=table(p);need(len(t)==416,'state count');g,m=canonical(t);need(g==x['graph_sha256'],'graph identity')
        norm=hashlib.sha256(json.dumps(sorted((q,b,w,d,z) for (q,b),(w,d,z) in t.items()),separators=(',',':')).encode()).hexdigest()
        need(norm==x['normalized_native_sha256'],'native normalization')
        order={q:i for i,q in enumerate(sorted({q for q,b in t}))};order[254]=208
        need(table(d)=={(order[q],b):(w,d,order[z]) for (q,b),(w,d,z) in t.items()},'dense renaming')
        groups.setdefault(g,[]).append((x,t,m));tabs[x['id']]=t
        startup,_=steps(t,0,0,set(),48140);startup['state']=m[startup['state']];starts[x['id']]=startup
    need(len(groups)==2,'graph classes')
    equations=0
    for members in groups.values():
        rx,rt,rm=members[0]
        for x,t,m in members:
            inv={v:q for q,v in rm.items()};f={q:inv[v] for q,v in m.items()}
            need(f[0]==0 and f[254]==254 and len(set(f.values()))==209,'rooted bijection')
            for (q,b),(w,d,z) in t.items():need(rt[f[q],b]==(w,d,f[z]),'conjugacy equation');equations+=1
            need(starts[x['id']]==starts[rx['id']],'complete startup')
    need(len({x['native_sha256'] for x in idx})==7,'byte variants')
    need(len({x['normalized_native_sha256'] for x in idx})==6,'native functions')
    need(len({x['source_sha256'] for x in idx})==2,'source variants')
    w=load('evidence/rejected207_witness.json');old=tabs['M9'];new=table('machines/rejected207.native.tm');need(len(new)==414,'rejected candidate count')
    need(sorted(frame(w['oldsite'][0],w['regs'],[0]))==w['initial_one_cells'],'witness frame')
    results={}
    for name,t in [('old',old),('new',new)]:
        source_path=idx[-1]['source_path'] if name=='old' else 'sources/rejected207.sites.json'
        site_addresses={x[0]:(i,x[1:]) for i,x in enumerate(load(source_path))}
        expected=w[name];out,tr=steps(t,84,0,w['initial_one_cells'],expected['steps'])
        need(out=={k:expected[k] for k in out},'counterexample endpoint '+name)
        need(hashlib.sha256(json.dumps(tr,separators=(',',':')).encode()).hexdigest()==expected['trace_sha256'],'trace digest '+name)
        need(decode_frame(out['state'],out['head'],out['ones'],site_addresses)==expected['decoded'],'full canonical endpoint '+name)
        # Verify this is the first clean canonical return, not an arbitrary observation time.
        ones=set(w['initial_one_cells']);q=84;h=0
        for k in range(expected['steps']):
            if k:need(decode_frame(q,h,ones,site_addresses) is None,'earlier full canonical return')
            b=int(h in ones);write,d,q=t[q,b]
            if write:ones.add(h)
            else:ones.discard(h)
            h+=1 if d=='R' else -1
        results[name]=out
    need(results['old']['ones']!=results['new']['ones'],'concrete contract failure')
    controls=[]
    if negative_controls:
        bad=dict(tabs['M9']);a=bad[0,0];bad[0,0]=(1-a[0],a[1],a[2])
        g,_=canonical(bad);need(g!=idx[-1]['graph_sha256'],'graph mutation escaped');controls.append('one-write graph mutation rejected')
        mutated=list(w['initial_one_cells']);mutated.remove(67)
        out,_=steps(new,84,0,mutated,w['new']['steps']);need(out['ones']!=w['new']['ones'],'witness mutation escaped');controls.append('initial-frame mutation rejected')
    return {'status':'PASS','scope':'pinned input comparison and rejected-candidate replay only','literal_tables':9,'working_states_each':208,'native_byte_variants':7,'normalized_native_functions':6,'graph_classes':2,'transition_equations':equations,'complete_startup_steps_each':48140,'rejected_candidate_working_states':207,'witness_parent_steps':results['old']['steps'],'witness_candidate_steps':results['new']['steps'],'negative_controls':controls}

def main():
    p=argparse.ArgumentParser();p.add_argument('--negative-controls',action='store_true');p.add_argument('--output');p.add_argument('--manifest',action='store_true');a=p.parse_args()
    if a.manifest:
        m=load('MANIFEST.json')
        for path,h in m['sha256'].items():need(sha(R/path)==h,'manifest '+path)
    r=replay(a.negative_controls);s=json.dumps(r,indent=2)+'\n'
    if a.output:Path(a.output).write_text(s)
    print(s,end='')
if __name__=='__main__':main()
