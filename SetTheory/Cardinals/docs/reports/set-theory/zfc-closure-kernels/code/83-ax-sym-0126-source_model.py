#!/usr/bin/env python3
"""Self-contained original203 source model and logical AX schema definitions.

Research code: state costs are measured source DAG costs, not TM bounds.
GEN and its cache read stay first. The C/G/vacuity bundle and gate stay last.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, json, random, sys, time, itertools

DATA_DIR=Path(__file__).resolve().parent/'data'
DATA=json.loads((DATA_DIR/'original203.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in DATA['nodes'].items()}

@lru_cache(None)
def bounds(e):
    if e[0]!='N': return (e[1] if e[0]=='B' else int(e[0]=='D'),e[1] if e[0]=='C' else 0)
    a,b=NODES[e[1]]; ba,ca=bounds(a);bb,cb=bounds(b)
    return max(ba-1,bb),max(ca,cb-1)

@lru_cache(None)
def normal(e):
    if e[0]!='N':return e
    a,b=NODES[e[1]];aa,bb=normal(a),normal(b)
    if bounds(a)==bounds(b)==(0,0):
        return ('S',*(aa[1:] if aa[0]=='S' else (aa,)),*(bb[1:] if bb[0]=='S' else (bb,)))
    return ('A',aa,bb)

def word(node):
    n=normal(('N',node))
    assert bounds(('N',node))==(0,0)
    return n[1:] if n[0]=='S' else (n,)

MACROS={166:word(43),121:word(48),168:word(63),171:word(39),177:word(91),
        119:word(57),181:word(79),180:word(58),182:word(57)+(('I',1),)*3,
        218:word(91)+word(57),176:word(60),158:word(18),208:word(30)}
MACROS[178]=MACROS[218]+MACROS[119]+MACROS[218]
MACROS[183]=MACROS[218]+MACROS[180]+MACROS[218]

def Imp(a,b):return ('imp',a,b)
def Rel(a,b):return ('rel',a,b)
def Eq(a,b):return ('eq',a,b)
def All(a,b):return ('all',a,b)
def Not(a):return Imp(a,1)
def Ex(a,b):return Not(All(a,Not(b)))
def emit(f):
    if f=='a':return [166]
    if f=='b':return [121]
    if f=='c':return [168]
    if f=='u':return [171,158,208]
    if f==0:return [171]
    if f==1:return [177]
    if f[0]=='imp' and f[2]==1:
        inner=f[1]
        if isinstance(inner,tuple) and inner[0] in ('imp','all') and isinstance(inner[2],tuple) and inner[2][0]=='imp' and inner[2][2]==1:
            return emit(inner[1])+emit(inner[2][1])+[178 if inner[0]=='imp' else 183]
        return emit(inner)+[218]
    return emit(f[1])+emit(f[2])+[{'imp':119,'rel':181,'eq':182,'all':180}[f[0]]]
from types import SimpleNamespace
theory=SimpleNamespace(emit=emit)
a,b,c,u,h='a','b','c','u','h'
ROWS=[All(a,h),Imp(Imp(Imp(c,u),a),Imp(Imp(a,c),Imp(b,c))),
      Imp(Eq(c,a),Imp(Eq(c,b),Eq(a,b))),Imp(Ex(a,All(a,b)),b),
      Imp(Eq(c,a),Imp(Rel(c,b),Rel(a,b))),
      Imp(All(a,All(b,c)),All(b,All(a,c))),
      Imp(Eq(a,b),Imp(Rel(c,a),Rel(c,b))),
      Imp(All(a,Imp(b,c)),Imp(All(a,b),All(a,c))),Ex(a,Eq(a,b))]
ROW_WORDS=[tuple(t for m in theory.emit(row) for t in MACROS[m]) for row in ROWS[1:]]
PREFIX=tuple(t for m in [166,121,180,176] for t in MACROS[m])

def regions():
    seqs={};atoms={}
    def go(t):
        if t[0]=='S':
            w=tuple(go(e) for e in t[1:])
            if w not in seqs:seqs[w]=len(seqs)
            return ('S',seqs[w])
        if t[0]=='A':
            p=go(t[1]),go(t[2])
            if p not in atoms:atoms[p]=len(atoms)
            return ('A',atoms[p])
        return t
    root=go(normal(('N',DATA['root'])))
    return {i:w for w,i in seqs.items()},{i:p for p,i in atoms.items()},root

SEQS,ATOMS,REGIONROOT=regions()
LONG=max(SEQS,key=lambda i:len(SEQS[i]))
# Map actual normal-form atoms onto the same sequence/control dictionary.
def map_normal(t):
    if t[0]=='S':
        v=tuple(map_normal(e) for e in t[1:])
        return ('S',next(i for i,w in SEQS.items() if w==v))
    if t[0]=='A':
        v=map_normal(t[1]),map_normal(t[2])
        return ('A',next(i for i,p in ATOMS.items() if p==v))
    return t
PREFIX=tuple(map_normal(t) for t in PREFIX)
ROW_WORDS=[tuple(map_normal(t) for t in row) for row in ROW_WORDS]
BEFORE=PREFIX+sum(ROW_WORDS,())
assert SEQS[LONG][:len(BEFORE)]==BEFORE, 'AX logical prefix does not equal original203'
SUFFIX=SEQS[LONG][len(BEFORE):]
ALPHABET=sorted(set(e for w in SEQS.values() for e in w))
ENCODE={e:i for i,e in enumerate(ALPHABET)}
BASEWORDS=[tuple(ENCODE[e] for e in SEQS[i]) for i in range(len(SEQS))]
PREFIX=tuple(ENCODE[e] for e in PREFIX)
ROW_WORDS=[tuple(ENCODE[e] for e in w) for w in ROW_WORDS]
SUFFIX=tuple(ENCODE[e] for e in SUFFIX)
