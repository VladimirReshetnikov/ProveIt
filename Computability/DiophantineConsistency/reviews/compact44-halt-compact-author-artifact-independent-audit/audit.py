#!/usr/bin/env python3
"""No-Lean audit of the six-source author-only halt-word receipt."""
import hashlib,importlib.util,json,os,pathlib,re,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';p=base/'compact44-halt-compact-audited-runner';plan=base/'compact44-halt-compact-audited-plan';ev=p/'evidence-author';out=P('/tmp/ipra-halt-compact-author-build-01');separate=P('/tmp/ipra-halt-compact-preflight-04');seed=P('/tmp/ipra-marked-suffix-final-build-01/lib');package=P('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');lean=P('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='7d02e879f6e8fca44751f0df40939793d1c70084ff2ad487bee25cad18c65e85'
assert H(p/'replay.py')=='24334eb297fcfb592e3a55d83985f63a25802adae66de39923d5509b0cc34763' and H(plan/'source-scan.json')=='a45508e7f15fca212f5be0db4055b15b01140d6a64ea2679eb65a9a9821d3585' and H(ev/'terminal-observation.json')=='b415c139fcea9e2390a8752feffb0437cfcaa8668d914ec313976d42e996bae9' and H(ev/'RESULT.json')==H(out/'RESULT.json')==want
term=json.loads((ev/'terminal-observation.json').read_bytes());result=json.loads((ev/'RESULT.json').read_bytes());pre=json.loads((ev/'preflight.json').read_bytes());rows=json.loads((plan/'source-scan.json').read_bytes())['sources'];steps=result['steps'];assert term['build']['session']==95103 and term['build']['outer_exit']==0 and term['build']['children']==6 and term['build']['compiler_exits_all_zero'] is True and term['build']['result_sha256']==want and term['preflight']['session']==70715 and term['preflight']['outer_exit']==0 and term['preflight']['lean_launched'] is False and term['lean_process_active_after'] is False
assert result['status']=='PASS_AUTHOR_ONLY_HALT_COMPACT_WORD' and len(rows)==len(steps)==len(pre['sourceguards'])==6 and len(pre['direct_companion_guards'])==160 and len(result['final_direct_and_output_slots'])==220
assert H(ev/'separate-preflight.json')==H(separate/'preflight.json')==term['preflight']['receipt_sha256'];assert json.loads((ev/'separate-preflight.json').read_bytes())['status']=='READY_AUTHOR_HALT_COMPACT_NO_LEAN'
for label,sha in [('parent','5e9daa236d9925f30789488f65d5ad9a89516147231a1810577f78f873351d0e'),('closure','b93af8ea96c6cab365bfa0e3d596a4fcbd473d914046a54d430de8611a156ad0')]:
 for moment in ('before','after'):assert result[label+'_audit_'+moment]=={'exit':0,'stdout_sha256':sha}
 assert pre[label+'_audit_before']==result[label+'_audit_before']
for name in ('preflight.json','progress.json','RESULT.json'):assert H(ev/name)==H(out/name)
for name in ('compact44-halt-audited-build01.stdout','compact44-halt-audited-build01.stderr','compact44-halt-audited-preflight04.stdout','compact44-halt-audited-preflight04.stderr'):assert (ev/name).read_bytes()==P('/tmp/'+name).read_bytes()
assert H(ev/'compact44-halt-audited-build01.stdout')==term['build']['stdout_sha256'] and H(ev/'compact44-halt-audited-build01.stderr')==term['build']['stderr_sha256'] and not (ev/'compact44-halt-audited-build01.stderr').read_bytes();assert H(ev/'compact44-halt-audited-preflight04.stdout')==term['preflight']['stdout_sha256'] and H(ev/'compact44-halt-audited-preflight04.stderr')==term['preflight']['stderr_sha256'] and not (ev/'compact44-halt-audited-preflight04.stderr').read_bytes()
assert json.loads((ev/'progress.json').read_bytes())['steps']==steps; stdout=(ev/'compact44-halt-audited-build01.stdout').read_text().splitlines();assert len(stdout)==8 and json.loads(stdout[0])=={'status':'READY_AUTHOR_HALT_COMPACT_NO_LEAN','sources':6,'guard_slots':160} and stdout[-1]=='PASS_AUTHOR_ONLY_HALT_COMPACT_WORD'
for step,line in zip(steps,stdout[1:-1]):assert json.loads(line)=={k:v for k,v in step.items() if k not in ('output_slots','axiom_reports')}
def checkslots(dic):
 for name,v in dic.items():
  q=P(name)
  if v is None:assert not os.path.lexists(q),name
  else:assert q.is_file() and str(q.resolve(strict=True))==v['realpath'] and H(q)==v['sha256'],name
checkslots(result['final_direct_and_output_slots']);checkslots(pre['direct_companion_guards'])
spec=importlib.util.spec_from_file_location('diag',plan/'diagnostic_policy.py');policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy);scan=json.loads((plan/'source-scan.json').read_bytes()); assert pre['sources']==rows and [x['module'] for x in rows]==[s['module'] for s in steps]
outputs={};details=[];counts=[];suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
for pos,(row,step) in enumerate(zip(rows,steps),1):
 name=row['module'];short=name.split('.')[-1];source=root/row['source'];frozen=(out/'frozen'/P(*name.split('.'))).with_suffix('.lean');saved=ev/'frozen'/P(*name.split('.'));saved=saved.with_suffix('.lean');obj=(out/'lib'/P(*name.split('.'))).with_suffix('.olean');log=out/(str(pos).zfill(3)+'-'+name.replace('.','_')+'.log');text=log.read_text();assert H(source)==H(frozen)==H(saved)==row['sha256']==pre['sourceguards'][str(frozen)] and not source.is_symlink() and not frozen.is_symlink();assert H(log)==H(ev/log.name)==step['log_sha256']
 assert step['position']==pos and type(step['compiler_exit']) is int and step['compiler_exit']==0 and step['reason'] is None and type(step['peak_sampled_rss_bytes']) is int and 0<step['peak_sampled_rss_bytes']<=int(3.5*1024**3) and step['command']==[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(out/'frozen'),str(frozen),'-o',str(obj)]
 count=text.count('warning:');counts.append(count)
 if short in policy.EXPECTED:
  b=scan['diagnostic_baselines'][short];hist=(root/b['historical_log']).read_text();assert H(root/b['historical_log'])==b['log_sha256']==policy.EXPECTED[short][1] and count==b['warning_count']==policy.EXPECTED[short][2];normalized=re.sub(r'(?m)^'+re.escape(str(frozen))+r'(?=:\d+:\d+: warning:)','<SOURCE>',text);historical=re.sub(r'(?m)^'+re.escape(policy.HISTROOT+short+'.lean')+r'(?=:\d+:\d+: warning:)','<SOURCE>',hist);assert normalized==historical and policy.validate(short,row['sha256'],str(frozen),text,hist)['warning_count']==count and step['axiom_reports']=={}
 else:
  assert short=='CompactHaltWord' and text=="'CompactHaltWord.halt_compact_word' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and policy.validate_client(text)==['propext','Classical.choice','Quot.sound'] and step['axiom_reports']=={'CompactHaltWord.halt_compact_word':['propext','Classical.choice','Quot.sound']}
 snap=step['output_slots'];assert set(snap)=={str(P(str(obj)[:-6]+suffix)) for suffix in suffixes} and obj.is_file() and not obj.is_symlink() and snap[str(obj)] is not None and all(v is None for k,v in snap.items() if k!=str(obj));checkslots(snap)
 mapping=pre['inputs'][name];assert set(mapping)==set(['Init']+row['imports']);expected=set()
 for dep,item in mapping.items():
  rel=P(*dep.split('.')).with_suffix('.olean');first=next((x for x in (out/'lib'/rel,package/rel) if x.is_file()),None);chosen=P(item['path']);assert first==chosen
  if item['kind']=='static':assert item['record']==result['final_direct_and_output_slots'][str(chosen)]
  else:assert item['kind']=='produced' and dep in outputs and result['final_direct_and_output_slots'][str(chosen)]==outputs[dep]
  expected.add(str(chosen.resolve()))
 assert {str(P(x).resolve()) for x in step['deps_stdout'].splitlines() if x.strip()}==expected
 outputs[name]=snap[str(obj)];details.append({'module':name,'source_sha256':row['sha256'],'object_sha256':H(obj),'log_sha256':H(log),'warning_count':count,'reports':step['axiom_reports']})
assert counts==[9,0,3,1,9,0] and term['build']['client_axiom_report']==['propext','Classical.choice','Quot.sound']
last=pre['inputs']['DiophantineConsistency.CompactHaltWord'];assert last['DiophantineConsistency.ArithmeticTilingWord']['kind']=='produced' and last['DiophantineConsistency.CompactWordDefinability']['kind']=='static' and P(last['DiophantineConsistency.CompactWordDefinability']['record']['realpath']).is_relative_to(seed)
def files(p):
 d={}
 for base,dirs,fs in os.walk(p,followlinks=False):
  assert all(not P(base,n).is_symlink() for n in dirs)
  for n in fs:d[P(base,n).relative_to(p).as_posix()]=P(base,n)
 return d
s=files(seed);a=files(out/'lib');new={str(P(*row['module'].split('.')).with_suffix('.olean')) for row in rows};assert len(s)==543 and len(a)==549 and not(set(s)&new) and set(a)==set(s)|new
for name,p0 in s.items():assert a[name].is_symlink() and a[name].resolve()==p0.resolve() and H(a[name])==H(p0)
print(json.dumps({'status':'PASS_INDEPENDENT_AUTHOR_ONLY_HALT_WORD_ARTIFACT_AUDIT','evidence_commit':'2d364a38c2','result_sha256':want,'source_modules':6,'source_rows':details,'warning_counts':counts,'guard_slots':220,'seed_files':543,'overlay_files':549,'client_axioms':steps[-1]['axiom_reports']['CompactHaltWord.halt_compact_word'],'lean_launched':False,'scope':'Single-author artifact audit; point-in-time direct guards and unauthenticated inherited transitive/package/dynamic ancestry; conditional model theorem, not graph zero, converse, tuple/K binding or internal PRA proof.'},indent=2,sort_keys=True))
