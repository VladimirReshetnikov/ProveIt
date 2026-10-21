#!/usr/bin/env python3
"""Replay independently checked Boolean and ternary source invariants."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys,tempfile
from check_zero_invariant import graph
ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'reproduced';OUT.mkdir(exist_ok=True)
subprocess.run([sys.executable,str(ROOT/'code/check_zero_invariant.py'),'--baseline',str(ROOT/'inputs/sites218.json'),'--candidate',str(ROOT/'candidates/zero_abstract_r6.sites.json'),'--invariant',str(ROOT/'certificates/zero_abstract_invariant.json'),'--output',str(OUT/'zero_boolean_verified.json')],check=True,capture_output=True,text=True)
rows=json.loads((ROOT/'inputs/sites218.json').read_text());edges=graph(rows);text=[str(len(rows))]
for (p,op,r),es in zip(rows,edges):
 text.append('{} {} {} {}'.format({'CI':0,'CD':1,'CB':2,'CC':2,'CH':3}[op],r if r is not None else 0,es[0]if es else -1,es[-1]if es else -1))
raw=('\n'.join(text)+'\n').encode();assert raw==(ROOT/'certificates/ternary_arithmetic_graph.tsv').read_bytes()
bitmap=gzip.decompress((ROOT/'certificates/zero_one_many.bin.gz').read_bytes());h=hashlib.sha256(bitmap).hexdigest();assert h=='4d8cd1c46705ea14998be21d3f3a67023371727d7cb5e6feba7d39c528ab08e3'
with tempfile.TemporaryDirectory(prefix='invariant-',dir=OUT)as t:
 temp=Path(t);(temp/'graph.tsv').write_bytes(raw);(temp/'bitmap.bin').write_bytes(bitmap);exe=temp/'check'
 subprocess.run(['c++','-std=c++17','-O2',str(ROOT/'code/check_ternary_certificate.cpp'),'-o',str(exe)],check=True)
 run=subprocess.run([str(exe),str(temp/'graph.tsv'),str(temp/'bitmap.bin')],check=True,capture_output=True,text=True);report=json.loads(run.stdout)
assert report['configurations']==5552082 and report['closure_edges']==6232731
report['bitmap_sha256']=h;report['independent_arithmetic_graph_sha256']=hashlib.sha256(raw).hexdigest();report['source_sha256']=hashlib.sha256((ROOT/'inputs/sites218.json').read_bytes()).hexdigest();report['scope']='Inductive closure from the seed class r0,r4>=2 and every other register zero. This is a source invariant, not a machine-fold proof.'
(OUT/'zero_ternary_verified.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
