#!/usr/bin/env python3
"""Reconstruct the twelve rotations and check the exact common-source simulation.

This is executable symbolic verification, not an exported Lean or PA proof.
Run with ordinary Python 3.10+; optimization mode is deliberately rejected.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import hashlib,json,sys
import source_language as s
import native_tools as b
import symbolic_core as c
HERE=Path(__file__).resolve().parent

def need(value,message):
    if not value:raise ValueError(message)

def graph(rows):
    a,_=s.graph_arithmetic(rows)
    need(a==s.graph_intervals(rows),'Independent CFG resolvers disagree')
    return a

def rewrite(tree,old,new):
    @lru_cache(None)
    def rec(t):
        if t==old:return new
        if s.leaf(t):return t
        return rec(t[0]),rec(t[1])
    return rec(tree)

def zero_runs(rows):
    return [i for i,(p,*_)in enumerate(rows)
            if '1000000' in p or p.startswith('0000000')]

def contracts(rows,instructions):
    path=lambda i:tuple(map(int,rows[i][0]))
    out=[]
    for i,ins in enumerate(instructions):
        initial=c.frame(path(i))
        if ins[0]=='inc':
            _,r,n=ins
            out.append((i,None,initial,c.canonical(c.frame(path(n),0,('x','inc',c.PHYSICAL[r])))))
        elif ins[0]=='dec':
            _,r,z,p=ins
            out.append((i,(c.PHYSICAL[r],True),initial,c.canonical(c.frame(path(z)))))
            out.append((i,(c.PHYSICAL[r],False),initial,c.canonical(c.frame(path(p),1,('x','dec',c.PHYSICAL[r])))))
        elif ins[0]=='jump':out.append((i,None,initial,c.canonical(c.frame(path(ins[1])))))
        else:out.append((i,None,initial,None))
    return out

def startup(table,steps,rows):
    q=74;head=0;tape=set();trace=hashlib.sha256()
    for tick in range(steps):
        read=int(head in tape);need((q,read)in table,'Premature startup halt')
        w,d,n=table[q,read]
        trace.update(f'{q},{head},{read},{w},{d},{n}\n'.encode())
        (tape.add if w else tape.discard)(head);head+=d;q=n
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    p=list(map(int,rows[25][0]))
    bits=p+[0]*(48-len(p))+[1]+[bit for v in physical for bit in [0]+[1]*(v+1)]
    expected={-1}|{i for i,v in enumerate(bits)if v}
    need(q==84 and {x-head for x in tape}==expected,'Startup does not reach the exact clean seed')
    return {'steps':steps,'native_state':q,'head':head,'source_ordinal':25,
            'header_gap':48,'physical_registers':physical,'trace_sha256':trace.hexdigest()}

def bisimulation_classes(table):
    states=sorted({q for q,_ in table});part={q:0 for q in states};part[254]=-1
    while True:
        keys={};new={254:-1}
        for q in states:
            key=tuple((w,d,part[n])for bit in(0,1)for w,d,n in[table[q,bit]])
            new[q]=keys.setdefault(key,len(keys))
        if all(part[q]==new[q]for q in states):return len(keys)
        part=new

def main():
    need(__debug__ and not sys.flags.optimize,'Run without -O or -OO')
    raw,labels=c.machine();old={k:(w,1 if right else -1,n)for k,(w,right,n)in raw.items()}
    original,instructions=c.program()
    code={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    rows=[[''.join(map(str,p)),code[op],arg]for p,op,arg in original]
    tree=s.tree(rows);original_graph=graph(rows);oldrows=rows
    table=old.copy();recipe=json.loads((HERE/'rotation_recipe.json').read_text())
    for step,(q,r,direction)in enumerate(recipe):
        groups,paths=b.decoder_map(table,tree)
        need(len(groups[q])==len(groups[r])==1,'A rotation state represents multiple subtrees')
        n=next(iter(groups[q]));need(n[direction]==next(iter(groups[r])),'Wrong rotation child')
        need(set(paths[r])=={p+str(direction)for p in paths[q]},'Shared child outside rotation')
        need(all(table[x,bit][:2]==(bit,1)for x in(q,r)for bit in(0,1)),'Reader is not pure')
        if direction==0:
            A,B=n[0];C=n[1];replacement=(A,(B,C))
            aa,bb,cc=table[r,0][2],table[r,1][2],table[q,1][2]
            changes={(q,0):(0,1,aa),(q,1):(1,1,r),(r,0):(0,1,bb),(r,1):(1,1,cc)}
        else:
            A=n[0];B,C=n[1];replacement=((A,B),C)
            aa,bb,cc=table[q,0][2],table[r,0][2],table[r,1][2]
            changes={(q,0):(0,1,r),(q,1):(1,1,cc),(r,0):(0,1,aa),(r,1):(1,1,bb)}
        need(s.boundary(A)[0]==s.boundary(C)[1]==0,'Directional escape condition fails')
        tree=rewrite(tree,n,replacement);table.update(changes)
        need(graph(s.sites(tree))==original_graph,f'CFG changed at rotation {step}')
        b.decoder_map(table,tree)
    rows=s.sites(tree)
    need(rows==json.loads((HERE/'sites.json').read_text()),'Source reconstruction mismatch')
    need(table==b.read_table((HERE/'machine.native.tm').read_bytes()),'Native reconstruction mismatch')
    for q in c.BOXSTATES:
        for bit in(0,1):need(table[q,bit]==old[q,bit],'Protected register-engine row changed')
    dense_labels=json.loads((HERE/'dense_labels.json').read_text())['dense_to_native']
    need(len(dense_labels)==197 and len(set(dense_labels))==197,'Bad dense labels')
    need(dense_labels[0]==74 and dense_labels[-1]==254,'Wrong start or halt mapping')
    dense={}
    for line in(HERE/'machine.tm').read_text().splitlines():
        q,bit,w,d,n=line.split();key=(int(q),int(bit));need(key not in dense,'Duplicate dense row')
        dense[key]=(int(w),1 if d=='R'else-1,int(n));need(d in('L','R'),'Bad direction')
    need(set(dense)=={(q,bit)for q in range(196)for bit in(0,1)},'Dense row domain')
    for(q,bit),(w,d,n)in dense.items():
        need(w in(0,1)and 0<=n<=196,'Bad dense action')
        need(table[dense_labels[q],bit]==(w,d,dense_labels[n]),'Dense/native mismatch')
    runtime=c.validate({k:(w,d==1,n)for k,(w,d,n)in table.items()},contracts(rows,instructions))
    need(runtime['ok'],'An arbitrary-register primitive contract failed')
    base=startup(old,58154,oldrows);new=startup(table,58294,rows)
    result={'status':'PASS','working_states':196,'rows':392,'rotations':len(recipe),
        'source_sites':len(rows),'source_cfg_equal_to_PA196':True,
        'independent_cfg_resolvers_agree':True,'symbolic_runtime':runtime,
        'protected_box_rows':2*len(c.BOXSTATES),'baseline_startup':base,'new_startup':new,
        'source_maximum_depth':s.metrics(tree)['maximum_depth'],
        'baseline_zero_scanner_obstruction_sites':zero_runs(oldrows),
        'new_zero_scanner_obstruction_sites':zero_runs(rows),
        'action_bisimulation_classes':bisimulation_classes(table),
        'dense_sha256':hashlib.sha256((HERE/'machine.tm').read_bytes()).hexdigest(),
        'native_sha256':hashlib.sha256((HERE/'machine.native.tm').read_bytes()).hexdigest(),
        'scope':'Executable whole-source simulation; no new exported Lean or PA theorem; not below196.'}
    (HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
