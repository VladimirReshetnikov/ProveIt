#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];N=D/'research/nine-sharing-sign31-direct-ipra-retry01';O=D/'research/nine-sharing-sign31-direct-ipra-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'90febb9284bb0ec2421bcd7e2e347d6c1fc2721174309f85bc8a38bbcb2d3645','source-manifest.json':'9d3a1e14e7962d84f91427b8114c08604240db62b2bfa9c7521ff88f0ffd0618','seed-data-survey.py':'a19191c2540184166ec49c103a228efb90631d0b17c6bc286c7cf1d4479c514c','partial-survey.py':'78b966aee13f8cba53c9c359860c7b8f51e7ba2668eb32cc134b5c0a6e2a67f8','framework-survey.py':'324fd79cc786f15ebbebd0d28bf4901123571eb850784dff516a8bd36d2211b3'}.items():assert sha(N/n)==h
m=json.loads((N/'source-manifest.json').read_text())['rows'];names=['Sign31AbstractExpressionDef','Sign31AbstractExpressionEval','Sign31CurrentExpressionDef','Sign31CurrentExpressionEval','Sign31CurrentExpressionSource','Sign31DirectIPRA'];assert [r['module'].split('.')[-1] for r in m]==names
for i,(row,n) in enumerate(zip(m,names)):
 p=N/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();orig=(O/'src/DiophantineConsistency'/f'{n}.lean').read_text();assert sha(p)==row['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports']
 if i==0:orig=orig.replace('import DiophantineConsistency.Sign31CurrentSourceIff','import DiophantineConsistency.SharingSeed31Sextic')
 if i==2:orig=orig.replace('import DiophantineConsistency.Sign31AbstractExpressionEval','import DiophantineConsistency.Sign31AbstractExpressionEval\nimport DiophantineConsistency.CurrentKernelData2011')
 assert s==orig
print(json.dumps({'status':'PASS_STATIC','scope':'six-stage retry changes two imports only; all source statements unchanged, no prior failed output used'}))
