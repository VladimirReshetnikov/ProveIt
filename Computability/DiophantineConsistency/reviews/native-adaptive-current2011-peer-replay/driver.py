from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'; REV=D/'reviews'
P=REV/'native-adaptive-current2011-replay.json'
MAN=REV/'native-adaptive-current2011-replay/FILES.json'
RECEIPT=REV/'native-adaptive-current2011-author.md'
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def require(x,msg):
 if not x:raise RuntimeError(msg)
def guard():require(shutil.disk_usage('/tmp').free>=512*1024**2,'512 MiB reserve')
pins={};observations=0
def check(r):
 global observations
 a=rec(r['path']);require(a['sha256']==r['sha256'],'hash '+r['path'])
 if a['path'] in pins:require(a==pins[a['path']],'conflicting pin '+a['path'])
 pins[a['path']]=a;observations+=1;return a
def parse_imports(p):
 text=Path(p).read_text();out=[];i=depth=0
 while i<len(text):
  pair=text[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(text) and text[i]!='\n':i+=1
  else:out.append(text[i]);i+=1
 require(depth==0,'unterminated comment')
 result=['Init']
 for line in ''.join(out).splitlines():
  m=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$',line)
  if m:result.extend(m[1].split())
 return list(dict.fromkeys(result))
guard();private=Path(tempfile.mkdtemp(prefix='native-adaptive-current2011-controller-peer-'))
lib=private/'lib';logs=private/'logs';lib.mkdir();logs.mkdir()
state={'status':'PREFLIGHT','private':str(private),'driver':rec(__file__),'records':[]}
save(private/'PEER.json',state)
Path('/tmp/native-adaptive-current2011-controller-peer-location.txt').write_text(str(private)+'\n')
print('PRIVATE',private,flush=True)
try:
 check(dict(path=str(P),sha256='9b7841844daed00727ec08fcdc81b6ab1a2952b62b68e03cffe37ba63bdb4b89'))
 check(dict(path=str(MAN),sha256='db4f52680f1c362cb7c987a087241fcc46d5dd8a83cd48e119f5f8b6d48bcbb9'))
 check(dict(path=str(RECEIPT),sha256='c355ecf2ba163f7d931bc0718c5223a3751d289012307f92f16d8b79eff3847b'))
 for row in json.loads(MAN.read_text()):check(row)
 author=json.loads(P.read_text());require(author['status']=='PASS','author state')
 inputs=json.loads(Path(check(author['inputs'])['path']).read_text())
 for p in inputs['pins']:check(p)
 for key in ['driver','plan','proposal','canonical_acceptance','canonical_manifest']:check(author[key])
 plan=json.loads(Path(author['plan']['path']).read_text())
 for p in plan['providers']:check(p)
 canonical=json.loads(Path(author['canonical_acceptance']['path']).read_text())
 require(canonical['status']=='PASS','canonical status')
 cm=Path(author['canonical_manifest']['path'])
 for r in json.loads(cm.read_text()):check(dict(r,path=str(cm.parent/r['path'])))
 for row in canonical['records']:
  for key in ['source','snapshot','object','log','timing']:check(row[key])
 selected=inputs['selected_custom'];external=inputs['external_boundary']
 require(len(selected)==377 and len(external)==64,'scope')
 require(sum(len(r['artifacts'])for r in external)==192,'boundary artifacts')
 byname={r['module']:r for r in selected};edge={r['module']:r for r in external}
 require(len(byname)==377 and len(edge)==64,'unique names')
 for row in selected:
  for key in ['source','object','original_object']:check(row[key])
  require(parse_imports(row['source']['path'])==row['actual_imports'],'header '+row['module'])
 for row in external:
  check(row['source'])
  for obj in row['artifacts']:check(obj)
 canonical_name='DiophantineConsistency.NativeAdaptiveCanonical'
 require(byname[canonical_name]['object']==canonical['records'][0]['object'],'canonical object supplement')
 require(set(byname)-{canonical_name}==set(plan['current']['custom_topological']),'plan closure')
 planned={r['module']:r for r in plan['selected_custom']}
 for n in set(byname)-{canonical_name}:
  for key in ['source','object','original_object','actual_imports']:
   require(byname[n][key]==planned[n][key],'planned provider '+n)
 seen=set();used=set();order=[];active=set()
 def visit(n):
  if n not in byname:require(n in edge,'unknown import '+n);used.add(n);return
  if n in seen:return
  require(n not in active,'cycle');active.add(n)
  for dep in byname[n]['actual_imports']:visit(dep)
  active.remove(n);seen.add(n);order.append(n)
 direct=['DiophantineConsistency.NativeAdaptiveCanonical','DiophantineConsistency.NativeOrdinarySourceConstruction']
 for n in direct:visit(n)
 require(seen==set(byname) and used==set(edge),'exact reachable DAG')
 targets=author['final']['records']
 for row in targets:
  for key in ['source','snapshot','object','log','timing']:check(row[key])
 require(parse_imports(targets[0]['source']['path'])==['Init',*direct],'main imports')
 require(parse_imports(targets[1]['source']['path'])==['Init',targets[0]['module']],'checks imports')
 for row in selected:
  dst=lib/Path(*row['module'].split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  dst.symlink_to(Path(row['object']['path']).resolve())
 paths=[str(lib),*inputs['LEAN_PATH'][1:]]
 require(all('/.lake/build/lib/lean' not in x or '/.lake/packages/' in x for x in paths),'shared project cache')
 provider_records=[]
 for row in selected+external:
  rel=Path(*row['module'].split('.')).with_suffix('.olean')
  first=next((Path(p)/rel for p in paths if (Path(p)/rel).exists()),None)
  require(first is not None,'missing provider '+row['module'])
  expected=row['object'] if 'object' in row else next(x for x in row['artifacts']if x['path'].endswith('.olean'))
  actual=rec(first);require(actual['sha256']==expected['sha256'],'provider '+row['module'])
  provider_records.append({'module':row['module'],'actual':actual,'expected':expected})
 check(inputs['compiler']);guard()
 evidence={'author_packet':rec(P),'author_manifest':rec(MAN),'author_receipt':rec(RECEIPT),
 'author_inputs':author['inputs'],'selected_custom':selected,'external_boundary':external,
 'pins':list(pins.values()),'topological_order':order,'actual_providers':provider_records,
 'compiler':inputs['compiler'],'LEAN_PATH':paths,'preflight_observations':observations}
 save(private/'INPUTS.json',evidence)
 shutil.copyfile(__file__,private/'driver.py');shutil.copyfile(author['driver']['path'],private/'author-driver.py')
 state.update(status='RUNNING',inputs=rec(private/'INPUTS.json'),counts=author['counts']);save(private/'PEER.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for old in targets:
  guard();check(old['source']);name=old['module'];short=name.split('.')[-1]
  out=lib/Path(*name.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  require(not out.exists() and not out.is_symlink(),'target must be fresh')
  snap=logs/(short+'.lean');shutil.copyfile(old['source']['path'],snap)
  log=logs/(short+'.log');timing=logs/(short+'.time')
  cmd=[inputs['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),old['source']['path']]
  start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'module':name,'source':old['source'],'snapshot':rec(snap),'command':cmd,'exit_code':code,
       'seconds':time.monotonic()-start,'log':rec(log),'timing':rec(timing)}
  state['records'].append(row);save(private/'PEER.json',state)
  require(code==0,'compiler '+name);require(out.is_file() and not out.is_symlink(),'regular output')
  text=log.read_text();require(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'diagnostics')
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
  require(json.loads(json.dumps(reports))==old['axiom_reports'],'axiom report mismatch')
  for n,a in reports:require(set(re.findall('[A-Za-z][A-Za-z.]*',a))<={'propext','Classical.choice','Quot.sound'},n)
  row.update(object=rec(out),axiom_reports=reports,
   object_byte_identical=rec(out)['sha256']==old['object']['sha256'],
   log_byte_identical=rec(log)['sha256']==old['log']['sha256'])
  require(row['object_byte_identical'] and row['log_byte_identical'],'object/log bytes differ')
  check(old['source']);guard();save(private/'PEER.json',state)
  print('PASS',short,round(row['seconds'],3),'reports',len(reports),flush=True)
 for p in list(pins.values()):check(p)
 for row in state['records']:
  for key in ['source','snapshot','object','log','timing']:check(row[key])
 state.update(status='PASS',unique_pins=len(pins),final_observations=observations,
   final_free_bytes=shutil.disk_usage('/tmp').free)
 save(private/'PEER.json',state);print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'PEER.json',state);raise
