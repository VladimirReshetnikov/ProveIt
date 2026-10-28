from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
PACKET=D/'reviews/arithmetic-binary-population-replay.json'
PLAN=D/'research/arithmetic-binary-population-cache-plan.json'
pins={};comparisons=0

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x,actual=None):
 global comparisons
 a=rec(actual or x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
 need('bytes'not in x or a['bytes']==x['bytes'],'size '+x['path'])
 pins[a['path']]=a;comparisons+=1;return a
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def imports(p):
 s=Path(p).read_text();o=[];i=depth=0
 while i<len(s):
  t=s[i:i+2]
  if depth:
   if t=='/-':depth+=1;i+=2
   elif t=='-/':depth-=1;i+=2
   else:o.append('\n'if s[i]=='\n'else' ');i+=1
  elif t=='/-':depth=1;i+=2
  elif t=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 need(depth==0,'comments');s=''.join(o)
 return list(dict.fromkeys(([]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init'])+[n for l in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in l.split()]))

guard();private=Path(tempfile.mkdtemp(prefix='arithmetic-binary-population-peer-'))
state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[])
save(private/'state.json',state);shutil.copyfile(__file__,private/'driver.py')
with Path('/tmp/arithmetic-binary-population-peer-runs.txt').open('a')as f:f.write(str(private)+'\n')
print('PRIVATE',private,flush=True)
try:
 check(dict(path=str(PACKET),sha256='ee47d164549eb378ed52ca616cc121ff50fc90f9e812f11f4419cd6616416677'))
 receipt=D/'reviews/arithmetic-binary-population-author.md'
 check(dict(path=str(receipt),sha256='77c2473a8b515006c7e64aa04cde1d463327192262f7c85a4b189dde9962e35d'))
 mf=D/'reviews/arithmetic-binary-population-author-replay/FILES.json'
 check(dict(path=str(mf),sha256='a7599395145ec4cbbe10aa7249aeb112e46cd12f0d60889ac5c2a07df17a0d1f'))
 manifest=json.loads(mf.read_text());need(len(manifest)==25,'25 evidence files')
 for x in manifest:check(dict(x,path=str(R/x['path'])))
 author=json.loads(PACKET.read_text());need(author['status']=='PASS','author PASS')
 for k in ['plan','plan_manifest','inputs','state','durable_state','driver','freeze_authentication','freeze_driver','independent_plan_receipt']:check(author[k])
 frozen=json.loads(Path(author['freeze_authentication']['path']).read_text())
 need(len(frozen['pins'])==2224,'author frozen paths')
 for x in frozen['pins']:check(x)
 check(dict(path=str(PLAN),sha256='8db28403220c05983a67306abafc73e78ee1fb85447948ab05ab584f29fae16e'))
 plan=json.loads(PLAN.read_text());profile=dict(custom=95,Foundation=95,artifacts=380,external=38,boundary_artifacts=114,actual_first_providers=494,fresh_prerequisites=0)
 need(plan['counts']==profile and author['counts']==profile,'profile')
 for x in plan['pins']:check(x)
 for x in json.loads(Path(author['plan_manifest']['path']).read_text()):check(dict(x,path=str(R/x['path'])))
 attempts=author['attempts'];need(len(attempts)==3,'three author attempts')
 texts=[];check_hashes=[]
 for i,attempt in enumerate(attempts):
  check(attempt['state']);check(attempt['durable_state']);st=json.loads(Path(attempt['state']['path']).read_text())
  need(st['status']==['FAILED','FAILED','PASS'][i] and attempt['status']==st['status'],'author chronology')
  check(st['driver']);check(st['inputs']);inp=json.loads(Path(st['inputs']['path']).read_text())
  source_map={s['path']:s['snapshot']['path']for s in inp['sources']}
  for x in inp['pins']:check(x,source_map.get(x['path']))
  for s in inp['sources']:check(s,s['snapshot']['path']);check(s['snapshot'])
  texts.append(Path(inp['sources'][0]['snapshot']['path']).read_text());check_hashes.append(inp['sources'][1]['sha256'])
  for k in ['plan','manifest','profile_reference','compiler']:check(inp[k])
  need(len(inp['actual_providers'])==494,'author first providers')
  for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
  for row in st['records']:
   need(row['source']['sha256']==row['snapshot']['sha256'],'snapshot binding')
   for k in ['snapshot','log','timing']:check(row[k])
   if 'object'in row:check(row['object'])
 need(len(set(check_hashes))==1,'checks unchanged across author attempts')
 need(re.sub(r'\bprefix\b','prefixCount',texts[0]).replace('←Arithmetic.sub_sub','Arithmetic.sub_sub')==texts[1],'only first author repair')
 base='case zero =>\n    constructor\n    · simpa only [zero_add,prefix_zero,fbit_two_mul_zero_eq_zero] using prefix_succ (0:V) (2*a)\n    · simpa only [zero_add,prefix_zero,fbit_two_mul_add_one_zero_eq_one] using prefix_succ (0:V) (2*a+1)'
 need(texts[1].replace('case zero => simp [prefix_succ]',base)==texts[2],'only second author repair')
 records=author['records'];need(records==st['records'],'final records')
 need(len(records)==2 and len(records[1]['axiom_reports'])==14,'fourteen reports')
 need([x['source']['sha256']for x in records]==['5ca0171ebc2525a1ac6f2fc3dbcd42c6793e935cd27f194b09501772511e6219','b1e882c8d79b3070d5a3ae638b0f11b412f8bc8af7f0517d3e648b036456bc38'],'exact final sources')
 for row in records:
  need(row['exit_code']==0,'final author exit')
  for k in ['source','snapshot','log','timing','object']:check(row[k])
 mods={x['module']:x for x in plan['modules']};ext={x['module']:x for x in plan['external']}
 seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:need(n in ext,'unknown '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle');active.add(n);m=mods[n]
  check(m['source']);need(imports(m['source']['path'])==m['imports'],'header '+n)
  for x in m['objects']:check(x)
  for n2 in m['imports']:visit(n2)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan['direct_imports']:visit(n)
 need(seen==set(mods)and used==set(ext)and order==plan['topological_order'],'complete DAG')
 for x in ext.values():
  check(x['source'])
  for a in x['artifacts']:check(a)
 need(imports(records[0]['source']['path'])==['Init',*plan['direct_imports']],'main imports')
 need(imports(records[1]['source']['path'])==['Init',records[0]['module']],'checks imports')
 check(plan['compiler']);guard()
 lib=private/'lib';logs=private/'logs';lib.mkdir();logs.mkdir()
 for m in mods.values():
  for obj in m['objects']:
   dest=lib/Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);need(not dest.exists(),'duplicate');dest.symlink_to(Path(obj['path']).resolve())
 paths=[str(lib),*plan['boundary_search']]
 need(all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in paths[1:]),'package-only fallback')
 providers=[]
 for m in list(mods.values())+list(ext.values()):
  for obj in m.get('objects',m.get('artifacts')):
   rel=Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
   found=next((Path(p)/rel for p in paths if(Path(p)/rel).is_file()),None)
   need(found is not None,'first provider missing')
   providers.append(dict(module=m['module'],expected=obj,actual=check(obj,found)))
 need(len(providers)==494,'all first providers');save(private/'providers.json',providers)
 for row in records:shutil.copyfile(row['source']['path'],logs/Path(row['source']['path']).name)
 inputs=dict(author_packet=rec(PACKET),author_manifest=rec(mf),author_receipt=rec(receipt),plan=rec(PLAN),compiler=plan['compiler'],counts=profile,LEAN_PATH=paths,providers=rec(private/'providers.json'),sources=[x['source']for x in records],pins=list(pins.values()),preflight_comparisons=comparisons)
 save(private/'inputs.json',inputs);state.update(status='RUNNING',inputs=rec(private/'inputs.json'),counts=profile);save(private/'state.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for author_row in records:
  source=author_row['source'];check(source);guard();short=author_row['module'].split('.')[-1]
  output=lib/Path(*author_row['module'].split('.')).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
  need(not output.exists()and not output.is_symlink(),'fresh output')
  log=logs/(short+'.log');timing=logs/(short+'.time');snapshot=logs/(short+'.lean');check(source,snapshot)
  command=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(output),source['path']]
  print('START',short,flush=True);start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=author_row['module'],source=source,snapshot=rec(snapshot),command=command,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
  state['records'].append(row);save(private/'state.json',state);print(log.read_text(),flush=True)
  need(code==0,'compiler '+short);need(output.is_file()and not output.is_symlink(),'regular output')
  need(output.stat().st_ino!=Path(author_row['object']['path']).stat().st_ino,'fresh independent inode')
  reports=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())]
  need(not re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()),'clean log')
  need(reports==author_row['axiom_reports'],'exact reports')
  for _,a in reports:need(set(re.findall('[A-Za-z][A-Za-z.]*',a))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  obj=rec(output);need(obj['sha256']==author_row['object']['sha256'],'exact object');need(row['log']['sha256']==author_row['log']['sha256'],'exact full log')
  row.update(object=obj,axiom_reports=reports,matches_author=True);save(private/'state.json',state);check(source)
 for x in list(pins.values()):check(x)
 guard();state.update(status='PASS',comparisons=comparisons,unique_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free);save(private/'state.json',state)
 print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'state.json',state);raise
