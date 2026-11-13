#!/usr/bin/env python3
"""Post-termination only; audit v6 attempt04 receipts and output, never starts Lean."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';O=P/'observations/attempt04';OUT=P/'observations/outer-attempt04';R=D/'reviews';PLAN=R/'ten-positive-80-127-rebuild-preflight/observations/attempt01.json';SCAN=R/'ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
def need(c,m):
 if not c:raise RuntimeError(m)
# No polling and no access to a live run: this atomic outer receipt is written after child exit.
need((OUT/'terminal.json').is_file(),'outer terminal absent: live or incomplete; do not use this post-run auditor')
outer=j(OUT/'terminal.json');r=j(O/'result.json');plan=j(PLAN);scan=j(SCAN)
need(outer['command'][1:4]==['-I','-S','-B'] and Path(outer['command'][4]).resolve()==(P/'run-v6.py').resolve() and outer['command'][5:]==['--attempt','attempt04'],'outer command')
need(sha(P/'run-v6.py')==outer['runner_sha256_before']==outer['runner_sha256_after']=='1956a0831c4dc93c5f30ff578ec6e7731c7d56f4be695d3ee8a7c4681a982298','runner pin')
need(sha(P/'run-v6-outer.py')=='8f159ccb6850fd8012900dcfd20d8fce0b037b764295ad3e1e6b279b64b47fed','outer wrapper pin')
need(sha(OUT/'stdout')==outer['stdout_sha256'] and sha(OUT/'stderr')==outer['stderr_sha256'],'outer logs')
need(sha(PLAN)=='cd224b6f17f9cd3cd08cf3a9e84923c1de9edbb635f6969cd4e1991e009b7e3a' and sha(SCAN)=='d65d7c776eb23425f9e2a290d8c3fdeebc011920619241290fdee85bc4ae68a9','plan/scan pin')
for p,digest in r['inputs'].items():need(sha(p)==digest,'input drift '+p)
need(sha(O/'initial-project.json')==r['initial_project_sha256'] and sha(O/'outside-baseline.json')==r['outside_baseline_sha256'],'baselines drift')
initial=j(O/'initial-project.json');outside=j(O/'outside-baseline.json');need(set(initial)==set(scan['project']) and set(outside)==set(scan['outside']),'baseline coverage')
for name,rec in initial.items():need(rec['.olean'] is not None and rec['.olean']['sha256']==scan['project'][name]['selected']['sha256'],'initial selected '+name)
for name,rec in outside.items():need(rec['.olean'] is not None and rec['.olean']['sha256']==scan['outside'][name]['sha256'],'outside selected '+name)
def verify_files(parts):
 need(parts.get('.olean') is not None,'missing olean in snapshot')
 stem=parts['.olean']['path'][:-6]
 for ext,rec in parts.items():
  q=Path(stem+ext);need(q.is_file()==(rec is not None),'companion presence drift '+str(q))
  if rec is not None:need(str(q)==rec['path'] and sha(q)==rec['sha256'] and str(q.resolve())==rec['resolved'],'file drift '+str(q))
for parts in initial.values():verify_files(parts)
for parts in outside.values():verify_files(parts)
# Every saved stage is validated, including an expected guarded failure at its terminal stage.
policies={
 'DiophantineConsistency.ArithmeticPellPigeonhole':('ebdbc22e239754f8f686be6971742d1b02560c9ffa35d464d2aecc323370765c','1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92','86cea8817e9e52731cc61a6b3b983a0635d96cc8dba13ea1743ae6bb82133d94',P/'warning-baseline-pigeonhole/baseline.txt'),
 'DiophantineConsistency.ModelArithmetic':('2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6','6af6ec8ca3ec1f14663f214b53f728a9a88b7b415ea8e68b769b27b197e44f0d','68e92da770d4ac5ff175531dfe6c334822a0a6d91e9af59f1e8f2ca56f2676e7',P/'warning-baseline-modelarithmetic/baseline.txt'),
 'DiophantineConsistency.ModelRatioBounds':('8ad9d28011406f9a8f2f6e8658405b4e582a7bdd224c83d2a2eb893a81116046','442a964429a3898a6110137b53268c9b370c60bb7de38899565d2885dd865c1b','1f7bad2e931bbfe6730e03be7b8963ac746b5bb76f44c7c6ebecaf238b35fc6e',P/'warning-baseline-ratiobounds/baseline.txt')}
for _,(_,h,_,p) in policies.items():need(sha(p)==h,'warning baseline drift')
stages=r['stages'];need([z['module'] for z in stages]==plan['ordered'][:len(stages)],'stage order');built={};exceptions=[]; outputroot=Path(r['output_root']);union=outputroot/'lib'
for idx,z in enumerate(stages,1):
 n=z['module'];need(z['index']==idx,'stage index');need(z['command'][1:4]==['-M3000','-j1','-DElab.async=false'],'flags '+n)
 # An interrupted stage may lack exit/log fields; report as incomplete, never accept it.
 if 'exit' not in z:
  need(r['status']!='PASS' and idx==len(stages),'incomplete stage in PASS');print('unfinished stage',idx,n,z.get('status'));break
 so=O/f'stage-{idx:03d}.stdout';se=O/f'stage-{idx:03d}.stderr';need(sha(so)==z['stdout_sha256'] and sha(se)==z['stderr_sha256'],'stage log '+n)
 src=next(Path(v) for v in z['command'] if v.endswith('.lean'));need(sha(src)==sha(plan['sources'][n]['source'])==z['source_sha256']==plan['sources'][n]['sha256'],'source '+n)
 need(z['preflight']['mem_available_kib']>=8*1024**2 and len(z['preflight']['lean'])<2,'preflight '+n)
 need(all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in z['samples']),'resource sample '+n)
 need(z.get('direct_before')==z.get('direct_after') and set(z['direct_before'])==set(scan['fresh_headers'][n]),'direct snapshot '+n)
 for dep,parts in z['direct_after'].items():
  verify_files(parts)
  want=(built[dep] if dep in built else initial[dep]) if dep in initial else outside[dep]
  need(parts['.olean']['sha256']==want['.olean']['sha256'],'selected dependency '+n+' '+dep)
  if dep in initial:need(Path(parts['.olean']['path'])==union/Path(dep.replace('.','/')+'.olean'),'project fell back '+dep)
  else:need(parts==outside[dep],'outside companion selection '+dep)
 text=so.read_text()+se.read_text();diagnostic=re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',text)
 if 'output' not in z:
  need(r['status']!='PASS' and idx==len(stages),'unaccepted stage in PASS');print('rejected stage',idx,n,'exit',z['exit'],'reason',z['reason'],'diagnostic',bool(diagnostic));break
 need(z['exit']==0 and z['reason'] is None,'accepted stage exit '+n)
 if diagnostic:
  need(n in policies,'unexpected diagnostic '+n);source,baseline,receipt,basepath=policies[n]
  need(z['source_sha256']==source and text.replace(str(src),'<SOURCE>')==basepath.read_text(),'warning text '+n)
  need(z.get('warning_exception',{}).get('baseline_sha256')==baseline and z['warning_exception'].get('receipt_sha256')==receipt,'exception record '+n);exceptions.append(n)
 else:need('warning_exception' not in z,'spurious exception '+n)
 verify_files(z['output']);built[n]=z['output'];print('stage',idx,n,z['output']['.olean']['sha256'])
if r['status']=='PASS':
 need(outer['exit']==0 and len(built)==len(stages)==127 and set(built)==set(plan['ordered']) and r['built']==built,'incomplete pass')
 # Recheck the final union for all project modules, including unrebuilt companions.
 for n,original in initial.items():
  expected=built.get(n,original);stem=union/n.replace('.','/')
  for ext,entry in expected.items():
   q=Path(str(stem)+ext);need(q.is_file()==(entry is not None),'final union presence '+n+ext)
   if entry is not None:need(sha(q)==entry['sha256'] and str(q.resolve())==entry['resolved'],'final union content '+n+ext)
 need(r['headers']=={n:scan['fresh_headers'][n] for n in plan['ordered']},'headers mismatch')
 batches=r['header_batches'];need(len(batches)==4,'header batch count')
 for k,h in enumerate(batches):
  so=O/f'headers-{k:03d}.stdout';se=O/f'headers-{k:03d}.stderr';need(h['exit']==0 and h['reason'] is None and sha(so)==h['stdout_sha256'] and sha(se)==h['stderr_sha256'] and not se.read_text(),'header receipt')
  need(h['preflight']['mem_available_kib']>=8*1024**2 and len(h['preflight']['lean'])<2 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in h['samples']),'header resource samples')
  expected=[str(union/(n.replace('.','/')+'.olean')) for n in plan['ordered'][k*32:(k+1)*32]];found={};current=None
  for line in so.read_text().splitlines():
   if line.startswith('BEGIN '):need(current is None and line[6:] in expected and line[6:] not in found,'header begin');current=line[6:];found[current]=[]
   elif line.startswith('IMPORT ') and current is not None:found[current].append(line[7:])
   elif line=='END' and current is not None:current=None
   else:raise RuntimeError('unexpected header line')
  need(current is None and set(found)==set(expected),'missing header')
  for n,path in zip(plan['ordered'][k*32:(k+1)*32],expected):need(found[path]==r['headers'][n],'header data '+n)
 endpoint=(O/'stage-127.stdout').read_text()+(O/'stage-127.stderr').read_text()
 for n in ('standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'):
  need(endpoint.count(f"'Direct80SymbolicFixedIPRA.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]")==1,'endpoint report '+n)
 print('PASS: 127 stages, direct dependencies, 4 header batches and 4 endpoint reports; exceptions',exceptions)
else:
 need(outer['exit']!=0 and r['status']=='FAILED','unexpected status/exit');print('FAILED as recorded:',r.get('failure'),'validated prior outputs',len(built))
print('outer sha',sha(OUT/'terminal.json'),'result sha',sha(O/'result.json'),'no Lean replay, package/transitive/external binding inherited')
