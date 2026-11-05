#!/usr/bin/env python3
"""Compare the first and replayed records and current guarded artifacts; no Lean."""
import hashlib,importlib.util,json,re
from pathlib import Path
root=Path(__file__).resolve().parents[4];task=root/'Computability/DiophantineConsistency'; p=task/'research/current14-mf-base-only-endpoint-replay'
first=Path('/tmp/current14-mf-base-only-attempt02-20261104'); replay=Path('/tmp/current14-mf-base-only-replay-20261104'); outer=Path('/tmp/current14-mf-base-only-replay-supervisor-20261104')
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
def read(x):return json.loads(Path(x).read_text())
def need(x,m):
 if not x:raise ValueError(m)
obs=read(p/'terminal-observation.json'); su=read(outer/'state.json'); x=read(first/'state.json'); y=read(replay/'state.json')
need(obs['observed_session_exit']==0 and obs['supervisor_state_sha256']==sha(outer/'state.json') and obs['runner_state_sha256']==sha(replay/'state.json'),'outer exit observation')
need(su['status']=='PASS' and su['child_exit']==0 and su['wait_interruptions']==[] and su['failure'] is None and su['replay_state_sha256']==sha(replay/'state.json'),'supervisor terminal')
need(su['supervisor_sha256']==sha(p/'supervisor.py')=='d1a61a05bd815afb109155be4985dedba39a15cece37a425e8e1fe88947169fa','supervisor source')
need(su['runner_sha256']==sha(p/'runner.py')==y['runner_sha256']=='988112f6ab8585dfa7eff62ce22d615d7faefa593eea1978b7d071ee638ed0ed','runner source')
need(sha(outer/'runner.log')==su['log_sha256'],'outer log')
need(x['status']==y['status']=='PASS' and x['initial']==y['initial']==su['initial']['base'] and sha(first/'state.json')==su['initial']['first_state_sha256'],'first/replay base linkage')
need([r['module'] for r in x['records']]==[r['module'] for r in y['records']]==['Current14LiteralPortsMF','StructuredEndpointMF'],'rows')
helper=task/'research/current14-printed-port-extension-driver-v3/guards.py'
need(sha(helper)=='e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3','guard helper')
spec=importlib.util.spec_from_file_location('guards',helper);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
comparisons=[]
for a,b in zip(x['records'],y['records']):
 n=a['module'];need(a['exit']==b['exit']==0 and a['source_sha256']==b['source_sha256'] and a['object_sha256']==b['object_sha256'] and a['axiom_reports']==b['axiom_reports'],'record mismatch '+n)
 da={k:v['sha256'] for k,v in a['direct_inputs'].items()};db={k:v['sha256'] for k,v in b['direct_inputs'].items()};need(da==db,'direct provider digests '+n)
 for rec,folder in ((a,first),(b,replay)):
  need(sha(folder/'src'/(n+'.lean'))==rec['source_sha256'] and sha(folder/'lib'/(n+'.olean'))==rec['object_sha256'],'source/object '+n)
  for f in ('log','stderr','deps_stdout','deps_stderr'):need(sha(rec[f])==rec[f+'_sha256'],'log '+n+f)
  for phase in ('deps_receipt','compile_receipt'):
   rr=rec[phase];need(rr['exit']==0 and rr['direct_child_reaped'] and rr['session_drained'],'child '+n)
  text=Path(rec['log']).read_text()+'\n'+Path(rec['stderr']).read_text();need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'bad log')
  g.check_guard(rec['direct_guards']);g.check_guard(rec['output_guards'])
 comparisons.append({'module':n,'source_sha256':a['source_sha256'],'object_sha256':a['object_sha256'],'direct_inputs':da,'axiom_reports':a['axiom_reports']})
need(comparisons==su['comparisons'],'recorded comparison')
need(comparisons[1]['axiom_reports']==[['Current14StructuredEndpointMF.recipe_endpoint','propext, Classical.choice, Quot.sound']],'endpoint axiom report')
print(json.dumps({'status':'PASS','outer_state_sha256':sha(outer/'state.json'),'replay_state_sha256':sha(replay/'state.json'),'review_script_sha256':sha(__file__),'scope':'Recorded same-provider replay and direct artifact linkage; no Lean or independent base rebuild.'},sort_keys=True))
