#!/usr/bin/env python3
"""No-Lean verification of the 22-source single-author suffix receipt."""
import hashlib,importlib.util,json,os,pathlib,re,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();research=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';pkg=research/'compact44-marked-suffix-final-author-runner';ev=pkg/'evidence-author-success';plan=research/'compact44-marked-suffix-final-source-plan';out=P('/tmp/ipra-marked-suffix-final-build-01');separate=P('/tmp/ipra-marked-suffix-final-preflight-02');seed=P('/tmp/ipra-wang-chunk-author-build-02/lib');package=P('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');lean=P('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='861109aea9162f2ba0573c640a0ba4dc1658e290ea7a620cdda39f1587695068'
assert H(pkg/'replay.py')=='d801e9fc26c028e134b1bd148044027adf8350613f3b849d2040cfe861476ee6' and H(plan/'source-scan.json')=='e90d141ec1083001b8d7504d9cc961ea5473fac79ea36f6cc090281651cd006b' and H(ev/'terminal-observation.json')=='d9a4697f9596993b57717602445becd57ed3e4375483615b2718693b94185868'
assert H(ev/'build-RESULT.json')==H(out/'RESULT.json')==want
term=json.loads((ev/'terminal-observation.json').read_bytes());result=json.loads((ev/'build-RESULT.json').read_bytes());pre=json.loads((ev/'build-preflight.json').read_bytes());rows=json.loads((plan/'source-scan.json').read_bytes())['sources'];steps=result['steps'];assert term['build_session']==74303 and term['build_outer_exit']==0 and term['accepted_children']==22 and term['compiler_exits_all_zero'] is True and term['result_sha256']==want and term['named_axiom_reports']==58 and term['final_inventory_reports']==16 and term['preflight_outer_exit']==0 and term['preflight_session']==75205
assert result['status']=='PASS_AUTHOR_ONLY_MARKED_SUFFIX' and len(rows)==len(steps)==pre['source_count']==22 and len(pre['direct_companion_slots'])==740 and len(result['final_direct_and_output_slots'])==960 and len(pre['source_pins'])==22
for label in ('before','after'):
 x=result['closure_audit_'+label];assert x['exit_code']==0 and x['stdout_sha256']=='b55a08a7efa315baa2973bbed07b1d1c5e9276663cd55e42f4f1cbbe0ba51134' and H(ev/('build-closure-audit-'+label+'.stdout'))==x['stdout_sha256'] and not (ev/('build-closure-audit-'+label+'.stderr')).read_bytes() and json.loads((ev/('build-closure-audit-'+label+'.json')).read_bytes())==x
for name in ('preflight.json','progress.json','RESULT.json'):assert H(ev/('build-'+name))==H(out/name)
assert H(ev/'preflight-preflight.json')==H(separate/'preflight.json')==term['preflight_receipt_sha256']
seppre=json.loads((ev/'preflight-preflight.json').read_bytes());assert seppre['status']=='READY_AUTHOR_ONLY_SUFFIX_NO_LEAN' and seppre['source_count']==22 and len(seppre['direct_companion_slots'])==740
sep=seppre['closure_audit_before'];assert sep['exit_code']==0 and sep['stdout_sha256']=='b55a08a7efa315baa2973bbed07b1d1c5e9276663cd55e42f4f1cbbe0ba51134' and H(ev/'preflight-closure-audit-before.stdout')==sep['stdout_sha256'] and not (ev/'preflight-closure-audit-before.stderr').read_bytes() and json.loads((ev/'preflight-closure-audit-before.json').read_bytes())==sep
for n in ('closure-audit-before.stdout','closure-audit-before.stderr','closure-audit-before.json'):assert H(ev/('preflight-'+n))==H(separate/n) and H(ev/('build-'+n))==H(out/n)
for n in ('closure-audit-after.stdout','closure-audit-after.stderr','closure-audit-after.json'):assert H(ev/('build-'+n))==H(out/n)
for target,original in [('ipra-marked-suffix-final-build-01.stdout','/tmp/ipra-marked-suffix-final-build-01.stdout'),('ipra-marked-suffix-final-build-01.stderr','/tmp/ipra-marked-suffix-final-build-01.stderr'),('ipra-marked-suffix-final-preflight-02.stdout','/tmp/ipra-marked-suffix-final-preflight-02.stdout'),('ipra-marked-suffix-final-preflight-02.stderr','/tmp/ipra-marked-suffix-final-preflight-02.stderr')]:assert (ev/target).read_bytes()==P(original).read_bytes()
assert not (ev/'ipra-marked-suffix-final-build-01.stderr').read_bytes() and not (ev/'ipra-marked-suffix-final-preflight-02.stderr').read_bytes()
assert json.loads((ev/'build-progress.json').read_bytes())['steps']==steps
stdout=(ev/'ipra-marked-suffix-final-build-01.stdout').read_text().splitlines();assert len(stdout)==24 and json.loads(stdout[0])['status']=='READY_AUTHOR_ONLY_SUFFIX_NO_LEAN' and stdout[-1]=='PASS_AUTHOR_ONLY_MARKED_SUFFIX'
for step,line in zip(steps,stdout[1:-1]):assert json.loads(line)=={k:v for k,v in step.items() if k not in ('output_slots','axiom_reports')}
def checkslots(dic):
 for name,record in dic.items():
  p=P(name)
  if record is None:assert not os.path.lexists(p),name
  else:assert p.is_file() and str(p.resolve(strict=True))==record['realpath'] and H(p)==record['sha256'],name
checkslots(result['final_direct_and_output_slots']);checkslots(pre['direct_companion_slots'])
spec=importlib.util.spec_from_file_location('reviewed_suffix_runner',pkg/'replay.py');runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner);baseline=runner.warning_baseline();assert set(baseline)=={'DiophantineConsistency.ArithmeticWangPlane','DiophantineConsistency.ArithmeticWangStrip','DiophantineConsistency.ArithmeticWangSoundness'}
outputs={};counts={};details=[];allcount=0;warnings={};allowed=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');assert [s['module'] for s in steps]==[x['module'] for x in rows]
for pos,(row,step) in enumerate(zip(rows,steps),1):
 name=row['module'];src=P(row['source']);frozen=(out/'frozen'/P(*name.split('.'))).with_suffix('.lean');obj=(out/'lib'/P(*name.split('.'))).with_suffix('.olean');log=out/(str(pos).zfill(3)+'-'+name.replace('.','_')+'.log');saved=ev/log.name
 assert H(src)==H(frozen)==row['sha256']==pre['source_pins'][str(frozen)] and not src.is_symlink() and not frozen.is_symlink()
 assert step['position']==pos and type(step['compiler_exit']) is int and step['compiler_exit']==0 and step['reason'] is None and type(step['peak_sampled_rss_bytes']) is int and 0<step['peak_sampled_rss_bytes']<=int(3.5*1024**3)
 assert step['compiler_command']==[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(out/'frozen'),str(frozen),'-o',str(obj)] and step['deps_command']==[str(lean),'--deps',str(frozen)]
 assert H(log)==H(saved)==step['log_sha256']; text=log.read_text(); wc=len(re.findall(r'(?m)^.*: warning:',text));
 if wc:warnings[name]=wc
 cleaned=runner.accepted_diagnostics(name,frozen,row['sha256'],text,baseline); reports=runner.report_inventory(frozen.read_text(),cleaned);assert reports==step['axiom_reports']
 if wc:assert name in baseline and text.replace(str(frozen),'<SOURCE>')==baseline[name] and cleaned==''
 pat=re.compile(r"(?m)^'([^']+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(does not depend on any axioms))");matches=list(pat.finditer(cleaned));independent={}
 for m in matches:
  key=m.group(1);assert key not in independent
  vals=[] if m.group(3) else [v.strip() for v in m.group(2).split(',') if v.strip()];assert len(vals)==len(set(vals)) and set(vals)<={'propext','Classical.choice','Quot.sound'} and (m.group(3) or vals);independent[key]=vals
 assert not pat.sub('',cleaned).strip() and independent==reports and set(independent)==set(re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',frozen.read_text(),re.M))
 n=len(reports);allcount+=n;counts[name]=n
 snap=step['output_slots'];assert len(snap)==10 and obj.is_file() and not obj.is_symlink() and snap[str(obj)] is not None and all(v is None for k,v in snap.items() if k!=str(obj)) and set(snap)=={str(P(str(obj)[:-6]+s)) for s in allowed};checkslots(snap)
 mapping=pre['direct_inputs'][name];expected=set();imports=re.findall(r'^import\s+([\w.]+)',frozen.read_text(),re.M);assert set(mapping)==set(['Init']+imports)
 for dep,item in mapping.items():
  rel=P(*dep.split('.')).with_suffix('.olean');first=next((x for x in (out/'lib'/rel,package/rel) if x.is_file()),None);chosen=P(item['path']);assert first==chosen
  if item['kind']=='static':assert item['record']==result['final_direct_and_output_slots'][str(chosen)]
  else:assert item['kind']=='produced' and dep in outputs and result['final_direct_and_output_slots'][str(chosen)]==outputs[dep]
  expected.add(str(chosen.resolve()))
 assert {str(P(x).resolve()) for x in step['deps_stdout'].splitlines() if x.strip()}==expected
 outputs[name]=snap[str(obj)];details.append({'module':name,'source_sha256':row['sha256'],'object_sha256':H(obj),'log_sha256':H(log),'axiom_reports':reports})
assert allcount==58 and counts['DiophantineConsistency.MarkedSuffixInventory']==16 and warnings==term['warnings'];assert set(steps[-1]['axiom_reports'])==set(re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',P(rows[-1]['source']).read_text(),re.M)) and all(set(v)=={'propext','Classical.choice','Quot.sound'} for v in steps[-1]['axiom_reports'].values())
assert pre['direct_inputs']['DiophantineConsistency.MarkedSuffixInventory']['DiophantineConsistency.CompactWordExistence']=={'kind':'produced','path':str(out/'lib/DiophantineConsistency/CompactWordExistence.olean')}
def files(p):
 d={}
 for base,dirs,fs in os.walk(p,followlinks=False):
  assert all(not P(base,x).is_symlink() for x in dirs)
  for x in fs:d[P(base,x).relative_to(p).as_posix()]=P(base,x)
 return d
s=files(seed);a=files(out/'lib');new={str(P(*r['module'].split('.')).with_suffix('.olean')) for r in rows};assert len(s)==521 and len(a)==543 and not(set(s)&new) and set(a)==set(s)|new
for name,p in s.items():assert a[name].is_symlink() and a[name].resolve()==p.resolve() and H(a[name])==H(p)
print(json.dumps({'status':'PASS_INDEPENDENT_AUTHOR_ONLY_FINAL_SUFFIX_ARTIFACT_AUDIT','evidence_commit':'772a5857ec','result_sha256':want,'source_modules':22,'source_rows':details,'named_reports':allcount,'final_inventory_reports':counts['DiophantineConsistency.MarkedSuffixInventory'],'warnings':warnings,'seed_files':len(s),'overlay_files':len(a),'guard_slots':len(result['final_direct_and_output_slots']),'lean_launched':False,'scope':'Single-author artifact audit, point-in-time direct object checks; no authenticated inherited transitive or dynamic package ancestry, paired replay, retained tuple/K binding, converse or internal PRA proof.'},indent=2,sort_keys=True))
