#!/usr/bin/env python3
"""Prove finite-table folds using inductive bit facts and symbolic open tapes.

A PASS proves a positive-block simulation on every binary tape from the declared old initial state.
The finite search limits bound proof construction, never the simulated run.
A NOT_PROVED result is not a counterexample to halting equivalence.
Standard library only. All checked facts are recomputed from the supplied bytes.
"""
from pathlib import Path
from collections import deque, Counter
import argparse, hashlib, json


def parse_table(data):
    t={};start=None
    for line in data.decode('utf-8').splitlines():
        if line.startswith('#! start '):start=int(line[9:])
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            if (q,b) in t or b not in (0,1) or w not in (0,1) or d not in ('L','R'):raise ValueError('Malformed table')
            t[q,b]=(w,1 if d=='R' else -1,z)
    qs={q for q,b in t}
    if set(t)!={(q,b) for q in qs for b in (0,1)}:raise ValueError('Incomplete table')
    if {z for w,d,z in t.values()}-qs!={254}:raise ValueError('Noncanonical inherited halt')
    if start not in qs:raise ValueError('Invalid start')
    return t,start


def table(path):
    return parse_table(Path(path).read_bytes())


def bit_invariant(t,start,radius):
    states={q for q,b in t}|{254};facts={q:None for q in states};facts[start]={}
    queue=deque([start]);queued={start}
    while queue:
        q=queue.popleft();queued.remove(q)
        if q==254:continue
        for b in (0,1):
            if 0 in facts[q] and facts[q][0]!=b:continue
            w,d,z=t[q,b];known={**facts[q],0:w}
            post={k-d:v for k,v in known.items() if -radius<=k-d<=radius}
            nf=post if facts[z] is None else {k:v for k,v in facts[z].items() if post.get(k)==v}
            if nf!=facts[z]:
                facts[z]=nf
                if z not in queued:queue.append(z);queued.add(z)
    if facts[start]!={}:raise ValueError('The start imposes tape constraints')
    checked=0
    for (q,b),(w,d,z) in t.items():
        if facts[q] is None or (0 in facts[q] and facts[q][0]!=b):continue
        post={k-d:v for k,v in {**facts[q],0:w}.items()}
        if facts[z] is None or any(post.get(k)!=v for k,v in facts[z].items()):raise ValueError('Invariant is not inductive')
        checked+=1
    return facts,checked


# An expression is a constant (None,0/1) or input cell (coordinate,xor_bit).
def xor(expr):return expr[0],expr[1]^1

def eval_expr(expr,known):
    v,neg=expr
    return (None,neg) if v is None else (None,known[v]^neg) if v in known else expr


def prove(old,new,oldstart,newstart,keep,drop,headshift,tagoffset,radius,fuel,branchcap):
    old_states = {q for q, b in old}
    new_states = {q for q, b in new}
    if drop not in old_states or keep not in new_states or keep == drop:
        raise ValueError('Fold must delete an old working state into a distinct retained working state')
    if oldstart == drop and tagoffset is not None:
        raise ValueError('The initial tape must not be transformed')
    phi=lambda q:keep if q==drop else q
    offset=lambda q:headshift if q==drop else 0
    if phi(oldstart)!=newstart or offset(oldstart)!=0:raise ValueError('Start configurations do not correspond')
    if set(q for q,b in new)!=(set(q for q,b in old)-{drop}):raise ValueError('Wrong deleted-state set')
    facts,checks=bit_invariant(old,oldstart,radius)
    def image_expr(q,h,p,oldwrite=None):
        e=(None,oldwrite) if oldwrite is not None and p==0 else (p,0)
        return xor(e) if q==drop and tagoffset is not None and p==h+tagoffset else e
    records=[];hist=Counter();total=0;max_leaves=0
    for (q,b),(w,d,z) in sorted(old.items()):
        if facts[q] is None or (0 in facts[q] and facts[q][0]!=b):continue
        known={**facts[q],0:b}
        initial={tagoffset:xor((tagoffset,0))} if q==drop and tagoffset is not None else {}
        todo=[(phi(q),offset(q),initial,known,0,[])];leaves=[];seen=0
        while todo:
            state,h,tape,env,steps,trace=todo.pop();seen+=1;total+=1
            if seen>branchcap:return {'status':'NOT_PROVED','old_row':[q,b],'reason':'branch cap','seen':seen}
            if steps:
                if z == 254 and state == 254:
                    leaves.append({'steps':steps,'guard':env,'trace':trace,'terminal':True})
                    hist[steps]+=1
                    continue
                positions=set(tape)|{0}
                if z==drop and tagoffset is not None:positions.add(d+tagoffset)
                equal=all(eval_expr(tape.get(p,(p,0)),env)==eval_expr(image_expr(z,d,p,w),env) for p in positions)
                if state==phi(z) and h==d+offset(z) and equal:
                    leaves.append({'steps':steps,'guard':env,'trace':trace});hist[steps]+=1;continue
            if state==254:return {'status':'NOT_PROVED','old_row':[q,b],'reason':'interior halt','trace':trace,'guard':env}
            if steps>=fuel:return {'status':'NOT_PROVED','old_row':[q,b],'reason':'block fuel','state':state,'head':h,'trace':trace,'guard':env}
            expr=eval_expr(tape.get(h,(h,0)),env)
            options=[(expr[1],env)] if expr[0] is None else [(read,{**env,expr[0]:read^expr[1]}) for read in(0,1)]
            for read,branch_env in options:
                nw,nd,nz=new[state,read]
                changed={**tape,h:(None,nw)}
                todo.append((nz,h+nd,changed,branch_env,steps+1,trace+[[state,h,read,nw,nd,nz]]))
        max_leaves=max(max_leaves,len(leaves))
        records.append({'row':[q,b],'branches':leaves})
    return {'status':'PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION','start_old':oldstart,'start_new':newstart,'halt':254,'old_states':len(old)//2,'new_states':len(new)//2,'keep':keep,'drop':drop,'headshift':headshift,'tagoffset':tagoffset,'invariant_radius':radius,'invariant_rows':checks,'invariant':facts,'proved_old_rows':len(records),'block_length_histogram':dict(sorted(hist.items())),'maximum_block':max(hist),'minimum_block':min(hist),'symbolic_configurations':total,'max_branches_per_row':max_leaves,'row_proofs':records,'scope':'All initial binary tapes and all integer head positions. Every old step maps to a positive new block, with no interior halt and exactly the mapped entire tape at nonhalting endpoints; terminal head/tape are immaterial.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('--keep',type=int,required=True);p.add_argument('--drop',type=int,required=True);p.add_argument('--headshift',type=int,default=0);p.add_argument('--tagoffset',type=int);p.add_argument('--radius',type=int,default=5);p.add_argument('--fuel',type=int,default=65);p.add_argument('--branchcap',type=int,default=20000);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    old_bytes=a.old.read_bytes();new_bytes=a.new.read_bytes()
    old,os=parse_table(old_bytes);new,ns=parse_table(new_bytes)
    out=prove(old,new,os,ns,a.keep,a.drop,a.headshift,a.tagoffset,a.radius,a.fuel,a.branchcap)
    out.update(old_sha256=hashlib.sha256(old_bytes).hexdigest(),new_sha256=hashlib.sha256(new_bytes).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('invariant','row_proofs','trace')},indent=2))
    if not out['status'].startswith('PASS'):raise SystemExit(1)
if __name__=='__main__':main()
