#!/usr/bin/env python3
"""Compare Lean graph source, coordinate leaves, and projected outputs to JSON."""
from pathlib import Path
from hashlib import sha256
import json,re,sys
if sys.flags.optimize: raise SystemExit('optimized Python refused')
here=Path(__file__).resolve().parent
src=(here/'XQ91.lean').read_text(); graph=json.loads((here/'candidate.json').read_bytes())
def parse(s):
    block=s.split('def graph (p : Fin 4 → ℤ) : Graph :=\n',1)[1].split('\nvariable {R',1)[0]
    lines=block.splitlines(); w=[]; ports=[]; rows=[]
    for line in lines:
        a=re.fullmatch(r'  let (\w+) : Expr \(Fin 12\) := \.var (\d+)',line)
        b=re.fullmatch(r'  let (\w+) : Expr \(Fin 12\) := \.constant \(p (\d+)\)',line)
        c=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
        if a:w.append((a.group(1),int(a.group(2))))
        elif b:ports.append((b.group(1),int(b.group(2))))
        elif c:
            n,x,op,y=c.groups();rows.append([n,op,int(x) if x.isdecimal() else x,int(y) if y.isdecimal() else y])
        elif line != '  ⟨A0, A1, N, P12⟩':raise ValueError('unrecognized graph line: '+line)
    if not lines or lines[-1]!='  ⟨A0, A1, N, P12⟩':raise ValueError('wrong projection')
    return w,ports,rows
def compare(s):
    w,p,r=parse(s)
    if w != list(zip(graph['witnesses'],range(12))):raise ValueError('witness mapping mismatch')
    if p != list(zip(graph['fixed_numerals'],range(4))):raise ValueError('port mapping mismatch')
    if r != graph['source']:raise ValueError('operation rows mismatch')
compare(src)
for name,mut in [('coordinate',src.replace('let w : Expr (Fin 12) := .var 5','let w : Expr (Fin 12) := .var 6',1)),
                 ('sign',src.replace('let kw := K0 + w','let kw := K0 - w',1)),
                 ('output',src.replace('⟨A0, A1, N, P12⟩','⟨A0, A1, A0, P12⟩',1))]:
    if mut==src:raise RuntimeError('mutation did not apply '+name)
    try:compare(mut)
    except ValueError:continue
    raise RuntimeError('mutation not rejected '+name)
print(json.dumps({'status':'PASS','rows':len(graph['source']),'witnesses':12,'ports':4,
                 'outputs':['A0','A1','N','P12'],'controls_rejected':['coordinate','sign','output'],
                 'lean_sha256':sha256(src.encode()).hexdigest(),
                 'graph_sha256':sha256((here/'candidate.json').read_bytes()).hexdigest()},indent=2))
