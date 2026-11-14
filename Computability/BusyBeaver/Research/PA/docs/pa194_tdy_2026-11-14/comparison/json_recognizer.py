#!/usr/bin/env python3
"""Literal JSON-table decoder adapted from the attributed QN packet scanner.
Source: docs/incoming/pa194qn_2026-11-14.zip,
pa194qn_2026-11-14/comparison/scanners/json_inventory.py at pinned repository
4be5c6e3a10292a7466f5d3687e3b39615ff049b. No generators are executed.
The surrounding corpus assembly and comparison are independent of that scanner.
"""
import re
from inventory import parse
def text_table(data):
    m=parse(data)
    if m is None:return None
    return validate(m[0])

def integer(x):
    return isinstance(x,int) and not isinstance(x,bool) and x>=0
def direction(x):
    return x in ('L','R',-1,1) and not isinstance(x,bool)
def normalized(x):
    w,d,t=x
    return w,('L' if d == -1 else 'R' if d == 1 else d),t
def action(x):
    return isinstance(x,list) and len(x)==3 and x[0] in (0,1) and direction(x[1]) and integer(x[2])
def validate(rows):
    if not rows:return None
    states={q for q,b in rows}
    if any((q,b) not in rows for q in states for b in (0,1)):return None
    halts={t for w,d,t in rows.values()}-states
    if len(halts)!=1:return None
    return rows,states,next(iter(halts))
def rowrecord(x):
    if not isinstance(x,dict):return None
    def get(names):
        for k in names:
            if k in x:return x[k]
        return None
    q=get(['state','source','q','current_state','from']); b=get(['read','symbol','read_bit','read_symbol','b'])
    w=get(['write','write_bit','write_symbol','w']); d=get(['direction','move','dir','d'])
    t=get(['next','target','next_state','to','t'])
    if integer(q) and b in (0,1) and w in (0,1) and direction(d) and integer(t):return q,b,w,d,t
def decode(node):
    if isinstance(node,str) and '\n' in node:
        return text_table(node.encode())
    rows={}
    if isinstance(node,list) and len(node)>=2:
        if all(isinstance(x,list) and len(x)==5 and integer(x[0]) and x[1] in (0,1) and x[2] in (0,1) and direction(x[3]) and integer(x[4]) for x in node):
            for q,b,w,d,t in node:
                if (q,b) in rows:return None
                rows[q,b]=normalized((w,d,t))
        elif all(isinstance(x,list) and len(x)==2 and all(action(a) for a in x) for x in node):
            rows={(q,b):normalized(a) for q,pair in enumerate(node) for b,a in enumerate(pair)}
        elif len(node)%2==0 and all(action(x) for x in node):
            rows={(i//2,i%2):normalized(x) for i,x in enumerate(node)}
        elif all(rowrecord(x) is not None for x in node):
            for q,b,w,d,t in map(rowrecord,node):
                if (q,b) in rows:return None
                rows[q,b]=normalized((w,d,t))
    elif isinstance(node,dict) and node:
        if all(k.isdigit() and isinstance(v,list) and len(v)==2 and all(action(a) for a in v) for k,v in node.items()):
            rows={(int(q),b):normalized(a) for q,pair in node.items() for b,a in enumerate(pair)}
        elif all(re.fullmatch(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?',k) and action(v) for k,v in node.items()):
            for k,v in node.items():
                q,b=map(int,re.findall(r'\d+',k));rows[q,b]=normalized(v)
    return validate(rows)

