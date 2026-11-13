#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-unscaled66-fresh-translated';O=P/'attempt02'; F=P/'attempt01';OUT=Path('/tmp/current2011-unscaled66-fresh-translated-v2-20261105');PRE=D/'reviews/current2011-unscaled66-fresh-base-independent';preflight=D/'research/normalized106-current14-sixteen-source-preflight/result.json'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'Translated138.lean':'f5593d902bfb493c25b6f6ed6ca8b5f2cfe11f93f570c6bc0b91ef51fe920650','check-client.py':'987c90bcbe15cf7bcc7ed6dd17627b199b18d308b2ae0ffbc64101cb252a04b8','attempt01/state.json':'22fcc066732a64d908f30b459bcac1075a5bb7f3fe9a371e792f0ff5856bc9a6','attempt01/outer-terminal.json':'126a0dc6c32e67f8580eaf3ab5e6e45afd976b2acd79e5cf2fe02d42341e468f','attempt02/state.json':'1fb8f44bcef7c2717aac985ee8d5ed7f39c278b14316f3d21240f17c44eda10e','attempt02/outer-terminal.json':'cf161d860a3e8f5eb3e7f5136b72a779818c038a3e41292309f9826c1e51dcae'}.items():need(H(P/n)==h,'pin '+n)
r=json.loads((O/'state.json').read_text());fail=json.loads((F/'state.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());ft=json.loads((F/'outer-terminal.json').read_text());need(r['status']=='PASS' and t['observed_session']==21034 and t['exit_code']==0 and t['state_sha256']==H(O/'state.json'),'successful exit');need(fail['status']=='FAILED' and ft['observed_session']==38776 and ft['exit_code']==1 and fail['runs'][-1]['exit']!=0,'failed attempt');need('sorryAx' in (F/'compile.txt').read_text() and 'Ambiguous term' in (F/'compile.txt').read_text(),'failed log');need(H(F/'compile.txt')==fail['runs'][-1]['log_sha256'],'failed log hash')
need(H(OUT/'state.json')==H(O/'state.json') and H(OUT/'Translated138.lean')==r['source_sha256']==H(P/'Translated138.lean'),'source and state');need(H(OUT/'Translated138.olean')==r['object_sha256']=='9a73122949dc09304251408cf0d10586634d390e5547bca6e8d1ee939c747cf5','object');need(len(r['direct_guard'])==100,'guard count')
for n,x in r['direct_guard'].items():
 p=Path(n)
 if x is None:need(not os.path.lexists(p),'unexpected '+n)
 else:need(p.is_file() and str(p.resolve())==x['realpath'] and H(p)==x['sha256'],'changed '+n)
need(set(r['dependencies'])=={'Init','Current2011Unscaled66Fresh'} and r['dependencies']['Current2011Unscaled66Fresh']['sha256']=='43de05d18c2854a224ebcd01c560cb5327752118ee08164277f38e7611a01b00','prior provider')
for n,x in r['dependencies'].items():need(r['direct_guard'][x['path']]['sha256']==x['sha256'],'direct link '+n)
for i,name in enumerate(('deps','compile')):need(r['runs'][i]['exit']==0 and H(O/(name+'.txt'))==r['runs'][i]['log_sha256'] and (O/(name+'.txt')).read_bytes()==(OUT/(name+'.txt')).read_bytes(),'log '+name)
log=(O/'compile.txt').read_text();need(log.count('depends on axioms:')==1 and all(x in log for x in ('propext','Classical.choice','Quot.sound')) and not any(x in log for x in ('sorryAx','warning:','error:')),'axioms');need(H(preflight)==r['preflight_before_sha256']==r['preflight_after_sha256'] and (OUT/'preflight-before.json').read_bytes()==preflight.read_bytes() and (OUT/'preflight-after.json').read_bytes()==preflight.read_bytes(),'preflight')
need(H(PRE/'check.py')=='091a2e546f3bd2ad63a09bf7704fa1dca90e66284b023ece4c8e432b2de0203a','prior checker pin');p=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'check.py')],capture_output=True);need(p.returncode==0 and p.stdout==(PRE/'result.json').read_bytes(),'prior source/objects audit rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','direct_slots':100,'prior_model_audit_exit':0,'failed_session':38776,'successful_session':21034,'scope':'Mapped Godel-Gentzen translated Foundation consistency, same 66 integer syntax; captured direct source/provider evidence, no Lean replay or new package-transitive ancestry.'},sort_keys=True,indent=2))
