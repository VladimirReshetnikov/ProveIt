#!/usr/bin/env python3
"""Read-only exact-delta review, no Lean invocation."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];A=D/'research/nine-sharing-norm38-check-sequence';B=D/'research/nine-sharing-norm38-check-retry01';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(A/'attempt01/state.json')=='019e5f01533f7ceebdf9744fcce99a851cca878b78438dd3891610c6e360db87','failed state');state=json.loads((A/'attempt01/state.json').read_text());need(state['status']=='FAILED' and len(state['rows'])==1 and state['failure']=="RuntimeError('compile failed SharingGateModel')",'failed scope');log=(A/'attempt01/SharingGateModel-compile.txt').read_text();need(sha(A/'attempt01/SharingGateModel-compile.txt')=='3c9cadd2f34fa0ec5432bd86788fef14122b732db1d0049932feeb4c23a516c7' and 'Unknown identifier `Function.update_same`' in log and 'Unknown identifier `Function.update_noteq`' in log,'failure log')
old=json.loads((A/'source-manifest.json').read_bytes());new=json.loads((B/'source-manifest.json').read_bytes());need(sha(B/'source-manifest.json')=='932be1171be69ad79a6279b776af15788ee5f9e7a417397e04d94a0608af345d' and len(old['rows'])==len(new['rows'])==6,'manifest');changes={}
for x,y in zip(old['rows'],new['rows']):
 need(x['module']==y['module'] and x['imports']==y['imports'],'module/import mismatch');n=x['module'].split('.')[-1]
 if n in ('SharingGateModel','SharingNormTrace'):
  a=(A/'src/DiophantineConsistency'/(n+'.lean')).read_text();b=(B/'src/DiophantineConsistency'/(n+'.lean')).read_text();need(a.count('Function.update_same')==(2 if n=='SharingGateModel' else 1) and a.count('Function.update_noteq')==(2 if n=='SharingGateModel' else 1),'replacement counts');need(b==a.replace('Function.update_same','Function.update_self').replace('Function.update_noteq','Function.update_apply'),'source delta');need(sha(B/'src/DiophantineConsistency'/(n+'.lean'))==y['source_sha256'],'new source hash');changes[n]=y['source_sha256']
 else:need(x==y,'unchanged row '+n)
oldrun=(A/'run.py').read_text();newrun=(B/'run.py').read_text();need(newrun==oldrun.replace('/tmp/nine-sharing-norm38-sequence-20261105','/tmp/nine-sharing-norm38-retry01-20261105').replace('860bc118705af6beb8c55f98036605506caa801460b058e4319791faa63304ac','932be1171be69ad79a6279b776af15788ee5f9e7a417397e04d94a0608af345d'),'runner delta');need(sha(B/'run.py')=='2dab121c54900c97abeed0072b96375f942f9e09b71872ea155db909c92b6fda','runner pin')
print(json.dumps({'status':'PASS_SOURCE_ONLY_RETRY_REVIEW','changed_sources':changes,'failed_compile_log_sha256':sha(A/'attempt01/SharingGateModel-compile.txt'),'scope':'Exact proof-identifier and runner delta; no Lean retry or theorem success claimed.'},indent=2,sort_keys=True))
