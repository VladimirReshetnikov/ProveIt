#!/usr/bin/env python3
"""Read-only literal 70-row Lean source / JSON comparison."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
GRAPH=HERE.parent/'current2011-ordinary70-84-candidate/polynomial.json'
SOURCE=HERE/'OrdinarySphere7084Literal.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
    if not v:raise RuntimeError(m)
need(sha(GRAPH)=='bb7df3586252e9c85be225a0373a8586c2c2f841683cc5f4b6f57f02175447e5','graph hash')
need(sha(SOURCE)=='e498fa16e97284c4d048460769d758d4f5b354e2cd9faa616c1857f84897e8ec','source hash')
g=json.loads(GRAPH.read_bytes());s=SOURCE.read_text();body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0]
variables=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',body,re.M)
ports=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',body,re.M)
need(variables==[(v,str(i)) for i,v in enumerate(g['witnesses'])],'variables')
need(ports==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])],'ports')
rows=[]
for name,a,op,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',body,re.M):
    rows.append([name,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b])
need(rows==g['source'] and body.rstrip().endswith('  polynomial'),'literal row mismatch')
print('PASS exact 70 graph rows, witness order and integer port aliases; no Lean replay')
