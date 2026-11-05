#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/normalized106-fresh-base-translated';O=P/'attempt02'; F=P/'attempt01';OUT=Path('/tmp/normalized106-fresh-model-translated-v2-20261105');PRE=D/'reviews/normalized106-fresh-base-model-independent';preflight=D/'research/normalized106-current14-sixteen-source-preflight/result.json'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'Translated106.lean':'3c73e83da63cd6acd1a041b3fe08cd22b05781426e820351f28d2db30fa6616b','check-translated.py':'1250d4914ed54bc212614996099a8d7afb56a49e78968ffcd89fbc25dc350b8d','attempt01/state.json':'c55af4d2535b88461cc7fb4e4711ffce498fcc876427f6384cb0050750aa9636','attempt01/outer-terminal.json':'917b8c318d225671ee6e1dbdf4fbe65c2e10e993a41ca08d9010cace6b58057f','attempt02/state.json':'76122622ac57776c6068f54b419a77e8ad7935675e9256a3f5ee1ea186eda3e7','attempt02/outer-terminal.json':'17ac58a37003dcbe9505e32d88678c25e97085392d55bfdb0db13f1d1a050479'}.items():need(H(P/n)==h,'pin '+n)
r=json.loads((O/'state.json').read_text());fail=json.loads((F/'state.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());ft=json.loads((F/'outer-terminal.json').read_text());need(r['status']=='PASS' and t['observed_session']==66668 and t['exit_code']==0 and t['state_sha256']==H(O/'state.json'),'successful exit');need(fail['status']=='FAILED' and ft['observed_session']==91078 and ft['exit_code']==1 and fail['runs'][-1]['exit']!=0,'failed attempt');need('sorryAx' in (F/'compile.txt').read_text() and 'positiveShift' in (F/'compile.txt').read_text(),'failed log');need(H(F/'compile.txt')==fail['runs'][-1]['log_sha256'],'failed log hash')
need(H(OUT/'state.json')==H(O/'state.json') and H(OUT/'Translated106.lean')==r['source_sha256']==H(P/'Translated106.lean'),'source and state');need(H(OUT/'Translated106.olean')==r['object_sha256']=='0957aebccbcb35f644a746c7dea67cbf7f6b253248f75c7827e40fd65132a233','object');need(len(r['direct_guard'])==80,'guard count')
for n,x in r['direct_guard'].items():
 p=Path(n)
 if x is None:need(not os.path.lexists(p),'unexpected '+n)
 else:need(p.is_file() and str(p.resolve())==x['realpath'] and H(p)==x['sha256'],'changed '+n)
need(set(r['dependencies'])=={'Init','FreshModel106'} and r['dependencies']['FreshModel106']['sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','prior provider')
for n,x in r['dependencies'].items():need(r['direct_guard'][x['path']]['sha256']==x['sha256'],'direct link '+n)
for i,name in enumerate(('deps','compile')):need(r['runs'][i]['exit']==0 and H(O/(name+'.txt'))==r['runs'][i]['log_sha256'] and (O/(name+'.txt')).read_bytes()==(OUT/(name+'.txt')).read_bytes(),'log '+name)
log=(O/'compile.txt').read_text();need(log.count('depends on axioms:')==1 and all(x in log for x in ('propext','Classical.choice','Quot.sound')) and not any(x in log for x in ('sorryAx','warning:','error:')),'axioms');need(H(preflight)==r['preflight_before_sha256']==r['preflight_after_sha256'] and (OUT/'preflight-before.json').read_bytes()==preflight.read_bytes() and (OUT/'preflight-after.json').read_bytes()==preflight.read_bytes(),'preflight')
need(H(PRE/'check.py')=='2f1e8f23caabe818d51ec8f3c56f6752794c9dee755624794cc8fb154a77361f','prior checker pin');p=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'check.py')],capture_output=True);need(p.returncode==0 and p.stdout==(PRE/'result.json').read_bytes(),'prior source/objects audit rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','direct_slots':80,'prior_model_audit_exit':0,'failed_session':91078,'successful_session':66668,'scope':'Mapped Godel-Gentzen translated Foundation consistency, same 106 syntax; captured direct source/provider evidence, no Lean replay or new package-transitive ancestry.'},sort_keys=True,indent=2))
