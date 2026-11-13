#!/usr/bin/env python3
"""Bind the 69 ordered source rows to the Lean DAG; not a Lean parser."""
import hashlib
import json
from pathlib import Path
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent
GRAPH=HERE.parent/'thirteen-variable-independent/polynomial69.json'
SOURCE=HERE/'Thirteen69Nodes.lean'
CUTS=HERE/'Thirteen69Cuts.lean'
EXPECTED='3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f'
VARS={'J':0,'F':1,'alpha':2,'f':3,'i':4,'T':5,'s':6,'w':7,'n':8,'eta':9,'zeta':10,'m':11,'gamma':12}
PORTS={'beta':0,'K0':1,'MC':2,'MF':3}

def require(cond,why):
    if not cond: raise ValueError(why)
def H(b): return hashlib.sha256(b).hexdigest()
def check(source,cuts,rows):
    require(source.count('section Generic\n')==1 and source.count('end Generic\n')==1,'generic section')
    block=source.split('section Generic\n',1)[1].split('end Generic\n',1)[0]
    actual=[line for line in block.splitlines() if line.startswith('def node_')]
    require(len(actual)==len(rows)==69,'exact node count')
    seen=set();used=set();operations={'*':0,'+':0,'-':0}
    def operand(x):
        if type(x) is int:
            require(x in (1,3,4),'numeric literal');return str(x)
        require(type(x) is str,'operand type');used.add(x)
        if x in VARS: return f'(v {VARS[x]})'
        if x in PORTS: return f'(p {PORTS[x]})'
        require(x in seen,'topological dependency '+x)
        return f'(node_{x} p v)'
    expected=[]
    for name,op,left,right in rows:
        require(isinstance(name,str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',name) and name not in seen,'node name')
        require(op in operations,'operation')
        expected.append(f'def node_{name} (p : Fin 4 → R) (v : Fin 13 → R) : R := {operand(left)} {op} {operand(right)}')
        operations[op]+=1;seen.add(name)
    require(actual==expected,'ordered exact source rows')
    require(operations=={'*':39,'+':16,'-':14},'operation histogram')
    require(set(VARS)|set(PORTS) <= used,'variable or port missing')
    require('def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n  node_polynomial (fun j => .constant (p j)) .var' in source,'literal output')
    require('def currentLiteral : Expr (Fin 13) := positiveShift (literal CurrentWindowCarry2011.ports)' in cuts,'2011 fixed shifted literal')
    require('theorem current_zero' in cuts and 'theorem scalar_eq' in cuts and 'theorem literal_value' in cuts,'compiled theorem interface')
    return operations

def main():
    raw=GRAPH.read_bytes();require(H(raw)==EXPECTED,'graph hash')
    graph=json.loads(raw);rows=graph['source'];src=SOURCE.read_text();cuts=CUTS.read_text()
    counts=check(src,cuts,rows)
    negatives=[]
    for old,new in [('* (v 0)','+ (v 0)'),('(p 0)','(p 1)'),('node_polynomial (fun j','node_product4 (fun j')]:
        require(old in src,'negative fixture absent')
        try:check(src.replace(old,new,1),cuts,rows)
        except ValueError:negatives.append(old)
        else:raise ValueError('mutation was accepted: '+old)
    try:check(src,cuts.replace('CurrentWindowCarry2011.ports','CurrentMasks2011.beta',1),rows)
    except ValueError:negatives.append('2011 port mutation')
    else:raise ValueError('port mutation accepted')
    print(json.dumps({'status':'PASS','graph_sha256':H(raw),'source_sha256':H(SOURCE.read_bytes()),'cuts_sha256':H(CUTS.read_bytes()),'rows':len(rows),'counts':counts,'negative_controls':negatives,'scope':'External exact source-row check; no general Lean parser, PDF binding, internal iPRA proof, or calibrated phase-split tuple is claimed.'},sort_keys=True))
if __name__=='__main__':main()
