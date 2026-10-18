#!/usr/bin/env python3
"""Finite source-control invariant over {0,1,>=2}, with unbounded values.

Transfer functions overapproximate all naturals. Starting at the supplied root,
monotone closure proves exclusions mathematically by induction on program
steps. This Python implementation has not been verified in Lean.
"""
from pathlib import Path
from collections import deque
import argparse,json
import rotation_search252 as r
import check_rotation252 as c

def analyze(nodes,root,initial_registers=None):
    leaves=[]
    def visit(e,p):
        if e[0]=='N':
            for b,x in enumerate(nodes[e[1]]):visit(x,p+str(b))
        else:leaves.append((p,e))
    visit(('N',root),'');index={p:i for i,(p,e) in enumerate(leaves)}
    def walk(pc):
        e=('N',root);path='';i=0
        while e[0]=='N':
            b=pc[i] if i<len(pc) else '0';i+=1;path+=b;e=nodes[e[1]][int(b)]
        assert not any(x=='1' for x in pc[i:])
        return index[path]
    edges=[];guardlist=[]
    for i,(p,e) in enumerate(leaves):
        row=[];op='C'+e[0];arg=e[1] if len(e)>1 else None
        for z in ((True,False) if op=='CD' else (None,)):
            npc=c.audit.successor(p,op,arg,z)
            nxt=None if op=='CH' else walk(npc or '')
            case=len(guardlist);guardlist.append((i,p,op,arg,z,nxt));row.append(case)
        edges.append(row)
    values=[0]*9 if initial_registers is None else initial_registers
    assert len(values)==9 and all(isinstance(v,int) and v>=0 for v in values)
    initial_masks=tuple(1 if v==0 else 2 if v==1 else 4 for v in values)
    masks=[None]*len(leaves);start=walk('');masks[start]=initial_masks;queue=deque([start]);pops=0
    def transfer(mask,op,arg,z):
        a=list(mask)
        if op=='CD':
            a[arg]&=1 if z else 6
            if not a[arg]:return None
            if not z:a[arg]=(1 if a[arg]&2 else 0)|(6 if a[arg]&4 else 0)
        if op=='CI':a[arg]=(2 if a[arg]&1 else 0)|(4 if a[arg]&6 else 0)
        return tuple(a)
    while queue:
        i=queue.popleft();pops+=1
        for case in edges[i]:
            _,p,op,arg,z,nxt=guardlist[case];after=transfer(masks[i],op,arg,z)
            if after is None or nxt is None:continue
            old=masks[nxt];new=after if old is None else tuple(x|y for x,y in zip(old,after))
            if new!=old:masks[nxt]=new;queue.append(nxt)
    excluded=[]
    for k,(i,p,op,arg,z,nxt) in enumerate(guardlist):
        after=None if masks[i] is None else transfer(masks[i],op,arg,z)
        if after is None:excluded.append({'case':k,'path':p,'op':op,'arg':arg,'zero':z,'masks':masks[i]})
        elif nxt is not None:assert all((a&b)==a for a,b in zip(after,masks[nxt]))
    return {'leaves':len(leaves),'guard_cases':len(guardlist),'worklist_pops':pops,'excluded':excluded,'masks':{p:masks[i] for i,(p,e) in enumerate(leaves)},'initial_registers':values,'initial_masks':initial_masks,'initial_state_included':all((a&b)==a for a,b in zip(initial_masks,masks[start])),'closure_checked':True,'abstraction':'bits1=zero,2=one,4=atleasttwo; componentwise product, unbounded natural values; exact finite control successors'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--dag',type=Path,default=r.HERE/'rotation-candidates/mp-cache252.json');ap.add_argument('--output',type=Path,default=r.HERE/'mp-cache252-phase.json');ap.add_argument('--initial-registers',help='Nine comma-separated logical register values; default all zero.');args=ap.parse_args()
    if not __debug__:ap.error('Assertions must remain enabled; do not use Python -O.')
    baseline=analyze(r.NODES,r.ROOT);assert [x['case'] for x in baseline['excluded']]==[8202,8203,8204,8358,8359,8360]
    initial=None if args.initial_registers is None else list(map(int,args.initial_registers.split(',')))
    d=json.loads(args.dag.read_text());ns={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};result=analyze(ns,d['root'],initial);result['baseline_six_exclusions_reproduced']=True;args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='masks'},indent=2))

if __name__=='__main__':main()
