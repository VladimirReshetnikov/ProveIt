#!/usr/bin/env python3
"""All-natural ordinal/register-store bisimulation via independent CFG resolvers."""
import json,hashlib
from pathlib import Path
import source_tools as s
ROOT=Path(__file__).resolve().parent.parent
def check(parent):
 old=json.loads((parent/'source/sites215.compact.json').read_text());new=json.loads((ROOT/'source/sites215.json').read_text());graphs=[];stats=[]
 for name,rows in [('parent',old),('alternative',new)]:
  t=s.tree(rows);a,n=s.graph_arithmetic(rows);b=s.graph_intervals(rows);assert a==b;graphs.append(a);stats.append(dict(name=name,metrics=s.metrics(t),six_zero_sites=sum('000000'in p for p,o,v in rows)))
 assert graphs[0]==graphs[1]and[x[1:]for x in old]==[x[1:]for x in new]and old[:37]==new[:37]
 return dict(status='ALL_NATURAL_SOURCE_BISIMULATION_PASS',stages=stats,guarded_cases=sum(2 if x[1]=='CD'else 1 for x in new),changed_PC_ordinals=sum(a[0]!=b[0]for a,b in zip(old,new)),guarded_CFG_sha256=hashlib.sha256(s.compact(graphs[0])).hexdigest(),theorem='Identity on instruction ordinal and arbitrary nine natural register values preserves every primitive effect, both decrement guards, every successor ordinal, and halt. Thus it is a strong step-for-step source bisimulation. The new blank seed has its separate calibration proof.')
