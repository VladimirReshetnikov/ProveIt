#!/usr/bin/env python3
"""Exact finite episode semantics allowing tape writes and reversals.

A summary consists of a decision diagram for terminal state/head and a finite
map of changed output cells, each itself a Boolean decision diagram. The
unmentioned output cells retain their initial symbols.
"""
import importlib.util,sys,json
from pathlib import Path
from functools import lru_cache

HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('pure_bdd',HERE/'decoder_bdd.py')
bd=importlib.util.module_from_spec(sp);sp.loader.exec_module(bd)
T=bd.T;states=bd.Tq
protected={2,4,6,48,63,73,83,95,109,112,131,255,75,60,44,31,56,38,40,28,64,69,96}
cuts=protected|{q for q in states if any(T[q,b][2]==q for b in (0,1))}
color={}
def visit(q):
    if q not in states or q in cuts:return
    color[q]=1
    for b in (0,1):
        r=T[q,b][2]
        if r not in states or r in cuts:continue
        if color.get(r)==1:cuts.add(r)
        elif not color.get(r):visit(r)
    color[q]=2
for q in sorted(states):
    if q not in color:visit(q)

def bit(b):return bd.leaf(-1,b)
def variable(i):return bd.node(i,bit(0),bit(1))
@lru_cache(None)
def shift_bool(i,d):
    a=bd.nodes[i]
    if a[0]=='leaf':
        assert a[1]==-1
        return i
    return bd.node(a[1]+d,shift_bool(a[2],d),shift_bool(a[3],d))

@lru_cache(None)
def summary(q):
    if q not in states or q in cuts:return bd.leaf(q,0),()
    cases=[]
    for b in (0,1):
        w,d,t=T[q,b]
        end,output=summary(t)
        end=bd.restrict(bd.shift(end,d),0,w)
        output={i+d:bd.restrict(shift_bool(v,d),0,w) for i,v in output}
        if 0 not in output:output[0]=bit(w)
        cases.append((end,output))
    lo,hi=cases
    end=bd.choose(0,lo[0],hi[0])
    outputs={}
    for i in lo[1].keys()|hi[1].keys():
        f=bd.choose(0,lo[1].get(i,variable(i)),hi[1].get(i,variable(i)))
        if f!=variable(i):outputs[i]=f
    return end,tuple(sorted(outputs.items()))

@lru_cache(None)
def restrict_summary(q,cube):
    end,output=summary(q)
    end=bd.cube(end,cube)
    output=tuple((i,v) for i,f in output if (v:=bd.cube(f,cube))!=bd.cube(variable(i),cube))
    return end,output

@lru_cache(None)
def depends(q,r):
    if q==r:return True
    if q not in states or q in cuts:return False
    return any(depends(T[q,b][2],r) for b in (0,1))

groups={}
for q in sorted(states):groups.setdefault(summary(q),[]).append(q)
hits=[qs for qs in groups.values() if len(qs)>1]
print(json.dumps(dict(transducer_cuts=sorted(cuts),bdd_nodes=len(bd.nodes),
    unconditional_hits=hits,largest_output_map=max(len(summary(q)[1]) for q in states)),indent=2))
