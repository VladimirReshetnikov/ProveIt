#!/usr/bin/env python3
"""No-Lean static and fake-control audit of corrected contextual row variants."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';HERE=Path(__file__).resolve().parent;PKG=BASE/'compact44-contextual-row-replays';COMMIT='e9bce4bbfa'
def need(c,msg):
 if not c:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
names=subprocess.run(['git','show','--format=','--name-only',COMMIT],cwd=ROOT,check=True,capture_output=True,text=True).stdout.splitlines()
need(len(names)==7,'unexpected corrected packet file count')
for name in names:
 blob=subprocess.run(['git','show',COMMIT+':'+name],cwd=ROOT,check=True,capture_output=True).stdout
 need(sha(blob)==sha((ROOT/name).read_bytes()),'corrected packet drift '+name)
expected={'compact44-inverse-lookup-prototype/contextual-replay.py':'37cd77db39cbdc732a80cec5ccc373a5cea05ac0ba6644788e2905525e5d7388','compact44-model-noextra-prototype/contextual-replay.py':'4e05a8a80989fc49fbd5a03f31f55e8e4681624d2520f3e9ba4a59fa36135913'}
for name,digest in expected.items():need(sha((BASE/name).read_bytes())==digest,'driver hash '+name)
for script,record in [('inverse-output-guard-fake.py','inverse-output-guard-controls.log'),('exclusion-output-guard-fake.py','exclusion-output-guard-controls.log')]:
 p=subprocess.run([sys.executable,'-I','-S','-B',str(PKG/script)],cwd=ROOT,capture_output=True,text=True,timeout=120)
 need(p.returncode==0 and not p.stderr and p.stdout==(PKG/record).read_text(),'fake-loop mismatch '+script)
p=subprocess.run([sys.executable,'-I','-S','-B',str(PKG/'contextual-row-preflight-controls.py')],cwd=ROOT,capture_output=True,text=True,timeout=120)
need(p.returncode==0 and not p.stderr and p.stdout==(PKG/'guard-observation.txt').read_text(),'parent/pin control mismatch')
p=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'output-controls.py')],cwd=ROOT,capture_output=True,text=True,timeout=120)
need(p.returncode==0 and not p.stderr and p.stdout.endswith('PASS no Lean launched\n'),'independent output controls')
obs=json.loads((HERE/'preflight-observation.json').read_text())
need(obs=={'inverse_session':70178,'inverse_exit':0,'exclusion_session':74251,'exclusion_exit':0,'historical_view':'/tmp/ipra-historical-audit-review-01','lean_launched':False},'preflight observation')
for kind,expected_statuses in [('inverse',['PASS_INDEPENDENT_COMPACT_ROW_MATCH_AUDIT']),('exclusion',['PASS_INDEPENDENT_COMPACT_ROW_MATCH_AUDIT','PASS_INDEPENDENT_COMPACT44_FORBIDDEN_AUDIT'])]:
 r=json.loads((HERE/(kind+'-parent-output.json')).read_text());need(r.get('status')=='PASS_CONTEXTUAL_ROW_READ_ONLY_PREFLIGHT' and r.get('kind')==kind and r.get('parent_statuses')==expected_statuses,'parent output '+kind)
print(json.dumps({'status':'PASS_INDEPENDENT_CONTEXTUAL_OUTPUT_GUARD_PREFLIGHT','reviewed_commit':COMMIT,'drivers':expected,'inverse_fake_modes':20,'exclusion_fake_modes':22,'output_slots_checked_each':10,'independent_parent_preflight_sessions':[70178,74251],'independent_parent_preflight_exits':[0,0],'lean_launched':False,'scope':'Corrected contextual historical-parent prelaunch review only; not unchanged live parent verification, Lean build, current-source binding, machine or PRA theorem. Point-in-time and inherited loader/package/resource boundaries remain.'},indent=2))
