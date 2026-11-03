#!/usr/bin/env python3
"""Compare explicit Lean register rows, pinned graph JSON, and PDF text."""
from hashlib import sha256
from pathlib import Path
import json,re,subprocess
H=Path(__file__).resolve().parent;D=H.parents[1]
SRC=H/'DisplayedRows.lean';GRAPH=D/'research/ten-positive-80-original-kernel-variant/equation.json'
PDF=D/'research/ten-positive-80-original-kernel-display/equation.pdf'
PINS={SRC:'fd36492f39119d761fb23adf835bc922c8e8ed092aed7e1ec88aac7b4844c585',
 GRAPH:'90bb24c77fab7a19cd4d021e7cd73eda527f71fc361b0aaba6a5f8eaeb1f7be2',
 PDF:'e6cba9c0124eeb35f0013ccde85753a2add8090ed390296f34227ffcfb544017'}
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
data=json.loads(GRAPH.read_text()); rows=data['source'];need(len(rows)==80,'graph count')
text=SRC.read_text();found=re.findall(r'^  let (r\d{2}) := (\w+) ([+*\-]) (\w+)$',text,re.M)
need(len(found)==80,'Lean register count')
variables=re.findall(r'^  let ([a-j]) : Expr \(Fin 10\) := \.var (\d+)$',text,re.M)
ports=re.findall(r'^  let (port\d) : Expr \(Fin 10\) := \.constant \(p (\d+)\)$',text,re.M)
need(variables==[(c,str(i)) for i,c in enumerate('abcdefghij')],'Lean variable slots')
need(ports==[(f'port{i}',str(i)) for i in range(4)],'Lean port slots')
need('  r80\n\ntheorem output_eq' in text,'Lean output slot')
refs=dict(zip(data['witnesses'],'abcdefghij'));refs.update(dict(zip(data['fixed_numerals'],('port0','port1','port2','port3'))))
for i,((name,op,a,b),(rn,la,lop,lb)) in enumerate(zip(rows,found),1):
 def conv(v):return str(v) if isinstance(v,int) else refs[v]
 need((rn,la,lop,lb)==(f'r{i:02}',conv(a),op,conv(b)),'Lean row mismatch '+str(i))
 refs[name]=rn
cmd=['pdftotext','-layout',str(PDF),'-'];p=subprocess.run(cmd,capture_output=True,text=True,check=True,timeout=60)
need(not p.stderr,'pdftotext stderr');page=p.stdout.split('\f')[0].replace('µ','μ')
pattern=r'\b(r\d{2})\s*=\s*(r\d{2}|[a-jβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-jβκμν]|\d+)'
found_pdf=re.findall(pattern,page);need(len(found_pdf)==80 and len({r[0] for r in found_pdf})==80,'PDF row count')
pdfrows={r[0]:r[1:] for r in found_pdf};varmap={'port0':'β','port1':'κ','port2':'μ','port3':'ν'};opmap={'+':'+','*':'·','-':'−'}
for rn,a,op,b in found:
 need(pdfrows[rn]==(varmap.get(a,a),opmap[op],varmap.get(b,b)),'PDF mismatch '+rn)
for p,h in PINS.items():need(sha(p)==h,'input changed after scan '+str(p))
print(json.dumps({'status':'PASS','rows':80,'source_sha256':sha(SRC),'graph_sha256':sha(GRAPH),
 'pdf_sha256':sha(PDF),'scope':'external exact Lean-row/JSON/PDF text comparison; no Lean compilation, PDF parser theorem or coefficient binding'},sort_keys=True))
