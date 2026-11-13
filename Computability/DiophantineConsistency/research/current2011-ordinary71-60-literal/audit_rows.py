#!/usr/bin/env python3
"""Read-only literal 71-row Lean source / JSON comparison."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
GRAPH=HERE.parent/'current2011-ordinary71-60-candidate/polynomial.json'
SOURCE=HERE/'OrdinarySphere7160Literal.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
    if not v:raise RuntimeError(m)
need(sha(GRAPH)=='3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27','graph hash')
need(sha(SOURCE)=='554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a','source hash')
g=json.loads(GRAPH.read_bytes());s=SOURCE.read_text();body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0]
variables=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',body,re.M)
ports=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',body,re.M)
need(variables==[(v,str(i)) for i,v in enumerate(g['witnesses'])],'variables')
need(ports==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])],'ports')
rows=[]
for name,a,op,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',body,re.M):
    rows.append([name,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b])
need(rows==g['source'] and body.rstrip().endswith('  polynomial'),'literal row mismatch')
print('PASS exact 71 graph rows, witness order and integer port aliases; no Lean replay')
