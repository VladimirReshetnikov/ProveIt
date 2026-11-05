#!/usr/bin/env python3
"""Read-only literal 66-row Lean source / JSON comparison."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
GRAPH=HERE.parent/'current2011-unscaled66/polynomial.json'
SOURCE=HERE/'Current2011Unscaled66.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
    if not v:raise RuntimeError(m)
need(sha(GRAPH)=='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75','graph hash')
need(sha(SOURCE)=='151dae72af79bf7d4714329ca3bda7a4b3308bb3e3a40d7ae3c14ae16bacd9a3','source hash')
g=json.loads(GRAPH.read_bytes());s=SOURCE.read_text();body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Eval',1)[0]
variables=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',body,re.M)
ports=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',body,re.M)
need(variables==[(v,str(i)) for i,v in enumerate(g['witnesses'])],'variables')
need(ports==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])],'ports')
rows=[]
for name,a,op,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',body,re.M):
    rows.append([name,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b])
need(rows==g['source'] and body.rstrip().endswith('  polynomial'),'literal row mismatch')
print('PASS exact 66 graph rows, witness order and integer port aliases; no Lean replay')
