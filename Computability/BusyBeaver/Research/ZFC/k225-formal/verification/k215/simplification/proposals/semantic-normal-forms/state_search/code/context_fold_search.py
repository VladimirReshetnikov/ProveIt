#!/usr/bin/env python3
"""Finite-context decoder folds and bounded exact-provider search.

The invariant phase is a finite proof by backwards transition preimages.
The provider phase branches on arbitrary exterior tape bits; a PASS is an
exact positive finite simulation, never a finite blank-run observation.
A failure or resource cap does not establish a TM state lower bound.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from collections import Counter, defaultdict
from pathlib import Path


def read_table(path):
    table = {}
    start = 0
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        if not line or line.startswith('#'): continue
        q,a,w,d,n = line.split()
        table[int(q),int(a)] = int(w), (1 if d=='R' else -1), int(n)
    states = sorted({q for q,a in table})
    assert len(table)==2*len(states)
    assert all((q,a) in table for q in states for a in (0,1))
    return table, start, states


def backward_impossible(pred, start, q, constraints, depth, node_cap):
    """All predecessors die by a write/read contradiction; initial tape arbitrary."""
    todo = [(q, constraints, 0)]
    nodes = 0
    max_depth = 0
    while todo:
        q,c,dep = todo.pop()
        nodes += 1
        if nodes > node_cap: return None
        if q==start or dep>=depth: return None
        max_depth=max(max_depth,dep)
        for p,a,w,d in pred[q]:
            # The previous head is at relative position -d.
            if -d in c and c[-d]!=w: continue
            prev = {j+d:v for j,v in c.items() if j!=-d}
            prev[0] = a
            todo.append((p,prev,dep+1))
    return {'nodes':nodes,'depth':max_depth+1}


def invariants(table,start,states,depth=8,node_cap=10000):
    pred=defaultdict(list)
    for (q,a),(w,d,n) in table.items(): pred[n].append((q,a,w,d))
    result={}
    proofs=[]
    for q in states:
        for a in (0,1):
            for marker in (0,1):
                cert=backward_impossible(pred,start,q,{0:a,-1:1-marker},depth,node_cap)
                if cert is not None:
                    proofs.append({'q':q,'read':a,'left':marker,**cert})
                    result[q,a]=marker
    return result,proofs


def pair_candidates(table,states,inv):
    pairs=[]
    for i,p in enumerate(states):
        for q in states[i+1:]:
            for a in (0,1):
                if table[p,1-a]!=table[q,1-a]: continue
                x,y=table[p,a],table[q,a]
                if x[:2]!=(a,1) or y[:2]!=(a,1) or x[2]==y[2]: continue
                if (p,a) not in inv or (q,a) not in inv: continue
                if inv[p,a]==inv[q,a]: continue
                pairs.append({'p':p,'q':q,'read':a,'left_p':inv[p,a],
                              'left_q':inv[q,a],'target_p':x[2],'target_q':y[2]})
    return pairs


def provider(table,pair,entry,write,move,marker,step_cap=96,cell_cap=10,node_cap=4096):
    p,q,a=pair['p'],pair['q'],pair['read']
    def phi(t): return p if t==q else t
    goal=phi(pair['target_p'] if marker==pair['left_p'] else pair['target_q'])
    todo=[(entry,move,{-1:marker,0:write},{-1:marker,0:a},0)]
    nodes=0
    max_steps=0
    while todo:
        state,h,tape,original,steps=todo.pop()
        nodes+=1
        if nodes>node_cap: return 'node_cap',nodes,max_steps
        if state==goal and h==1 and tape==original:
            max_steps=max(max_steps,steps+1)
            continue
        if steps>=step_cap: return 'step_cap',nodes,max_steps
        if state==q or (state,0) not in table: return 'halt_or_missing',nodes,max_steps
        if h not in tape:
            if len(tape)>=cell_cap: return 'cell_cap',nodes,max_steps
            for b in (0,1):
                t,o=tape.copy(),original.copy()
                t[h]=o[h]=b
                todo.append((state,h,t,o,steps))
            continue
        b=tape[h]
        if state==p and b==a: w,d,n=write,move,entry
        else:
            w,d,n=table[state,b]
            n=phi(n)
        t=tape.copy();t[h]=w
        todo.append((n,h+d,t,original,steps+1))
    return 'PASS',nodes,max_steps


def joint_two_step(table,states,pairs):
    """Two disjoint folds share one new selector; net saving one state."""
    hits=[];attempts=0
    for i,a in enumerate(pairs):
        for b in pairs[i+1:]:
            if len({a['p'],a['q'],b['p'],b['q']})!=4: continue
            if a['read']==b['read']: continue
            attempts+=1
            def targets(pair,m):
                return pair['target_p'] if pair['left_p']==m else pair['target_q']
            def providers(m):
                return [s for s in states if s not in {a['p'],a['q'],b['p'],b['q']}
                  and table[s,a['read']]==(a['read'],1,targets(a,m))
                  and table[s,b['read']]==(b['read'],1,targets(b,m))]
            x,y=providers(0),providers(1)
            if x and y: hits.append({'first':a,'second':b,'left0_providers':x,'left1_providers':y})
    return {'pairs_examined':attempts,'hits':hits}


def run(path,depth=8,step_cap=96,cell_cap=10,node_cap=4096,fast=False):
    table,start,states=read_table(path)
    started=time.monotonic()
    inv,proofs=invariants(table,start,states,depth)
    pairs=pair_candidates(table,states,inv)
    stats=Counter();hits=[];trials=0;nodes=0
    for pair in pairs:
        for write in (0,1):
            for move in (-1,1):
                for entry in states:
                    if entry==pair['q']:continue
                    trials+=1
                    first,n,t0=provider(table,pair,entry,write,move,0,step_cap,cell_cap,node_cap)
                    nodes+=n;stats[first]+=1
                    if first!='PASS':continue
                    second,n,t1=provider(table,pair,entry,write,move,1,step_cap,cell_cap,node_cap)
                    nodes+=n;stats['second_'+second]+=1
                    if second=='PASS':
                        hits.append({'pair':pair,'entry':entry,'write':write,'move':move,
                                     'max_duration':max(t0,t1)})
                        if fast:break
    return {'input':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'start':start,'working_states':len(states),'invariant_count':len(proofs),
            'invariants':proofs,'eligible_pairs':pairs,'provider_trials':trials,
            'symbolic_nodes':nodes,'stats':dict(stats),'hits':hits,
            'joint_two_step':joint_two_step(table,states,pairs),
            'bounds':{'backwards_depth':depth,'steps_after_first':step_cap,
                      'visited_cells':cell_cap,'symbolic_nodes_per_case':node_cap},
            'elapsed_seconds':time.monotonic()-started,
            'scope':'No successful reduction is a result only for this bounded template; not a state lower bound.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--steps',type=int,default=96);ap.add_argument('--cells',type=int,default=10);ap.add_argument('--depth',type=int,default=8)
    args=ap.parse_args();res=run(args.table,args.depth,args.steps,args.cells)
    args.output.write_text(json.dumps(res,indent=2)+'\n')
    print(json.dumps({k:res[k] for k in ['sha256','working_states','invariant_count','provider_trials','symbolic_nodes','stats','hits','joint_two_step','bounds','elapsed_seconds']},indent=2))
