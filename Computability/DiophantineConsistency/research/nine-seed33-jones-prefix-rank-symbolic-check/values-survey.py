#!/usr/bin/env python3
"""Authenticate two audited groups and their selected routes into the composition overlay."""
import hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-seed33-jones-prefix-rank-composition-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();observed={}
items=[('02','64adc92ea6a031a7054da32199c190b50e63ab4eb5046e4151dbd993f7e73b67','8c2739650a6d46afb1b3c3a9000610380150262c79ce9e350d508138108c4166','ab40f9812a6ec480f34c57d62a52bced398dbbffe27d4f0f897df61ee24edf28',['Sign33MacroPrefixE','Sign33MacroPrefixEll','Sign33MacroPrefixLambda']),('03','f1769a73743919a3ff52d3637a514592fdbd5d5222669bc17c404ecee33a29d0','ab4237754322f7aa5c7c769ce0068235e656272fc30a2f7e7910ab2559de8c22','7a5f8787056d592aac8507aa66807fe3919af3b570326a483077997258741da2',['Sign33MacroPrefixGsmall','Sign33MacroPrefixTheta'])]
for g,statehash,checker,result,names in items:
 audit=D/f'reviews/nine-seed33-jones-prefix-group{g}-staged-terminal-frontier-independent';assert H(audit/'check.py')==checker and H(audit/'result.json')==result
 run=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True,text=True,timeout=120);assert run.returncode==0 and json.loads(run.stdout)['status']=='PASS_TERMINAL_AUDIT'
 state=D/f'research/nine-seed33-jones-prefix-group{g}-staged-check/attempt01/state.json';assert H(state)==statehash;s=json.loads(state.read_text());assert s['status']=='PASS'
 for name in names:
  rr=[x for x in s['rows'] if x['module']==name];assert len(rr)==1;r=rr[0];original=Path(f'/tmp/nine-seed33-jones-prefix-group{g}-staged-check-20261106/lib/DiophantineConsistency')/(name+'.olean');q=BASE/'lib/DiophantineConsistency'/(name+'.olean');assert q.is_file() and q.resolve()==original.resolve() and H(q)==r['object_sha256'];observed[name]={'sha256':r['object_sha256'],'realpath':str(q.resolve())}
print(json.dumps({'status':'PASS','observed':observed,'scope':'Five audited producer routes into d11 overlay; deeper ancestry inherited.'},sort_keys=True))
