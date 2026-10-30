"""Private structural type audit against a provenance-qualified historical object."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[2]
B=Path(os.environ.get('WANG_SPLIT_TABLE','/tmp/adaptive-wang-table-split-b9zuak6s'))
C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl')
H=Path('/tmp/construction-share/pinned-final/DiophantineConsistency/ArithmeticWangTable.olean')
T='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
bs=read(B/'state.json');cs=read(C/'state.json');hs=read(R/'reviews/adaptive-assembly-historical2011-evidence/state.json')
g=read(C/'guards.json');providers=read(C/'providers.json');chunk=Path(bs['chunk_provider']);ck=read(chunk/'state.json');Q=Path('/tmp/adaptive-wang-chunk-full-src/DiophantineConsistency')
assert bs['status']==cs['status']==ck['status']=='PASS'
assert sha(C/'guards.json')==bs['guards_sha256']==cs['guards_sha256']
assert sha(C/'providers.json')==bs['providers_sha256']==cs['providers_sha256']
assert sha(chunk/'state.json')==bs['chunk_state_sha256']
historical_hash=sha(H); table_hash=sha(B/'lib/DiophantineConsistency/ArithmeticWangTable.olean');assert table_hash==bs['object_sha256']
base_hash=sha(B/'state.json');hist_state_hash=sha(R/'reviews/adaptive-assembly-historical2011-evidence/state.json')
def auth():
 return (sha(B/'state.json')==base_hash and sha(chunk/'state.json')==bs['chunk_state_sha256'] and sha(H)==historical_hash
   and sha(B/'lib/DiophantineConsistency/ArithmeticWangTable.olean')==table_hash
   and sha(R/'reviews/adaptive-assembly-historical2011-evidence/state.json')==hist_state_hash
   and sha(C/'guards.json')==bs['guards_sha256'] and sha(C/'providers.json')==bs['providers_sha256']
   and all(sha(p)==h for p,h in g.items()) and all(sha(x['path'])==x['sha256'] for x in providers.values())
   and all(sha(Q/(x['name']+'.lean'))==x['source_sha256'] and sha(chunk/'lib/DiophantineConsistency'/(x['name']+'.olean'))==x['object_sha256'] and sha(chunk/'logs'/(x['name']+'.log'))==x['log_sha256'] for x in ck['records']))
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-wang-export-enumeration-'));shutil.copyfile(__file__,w/'driver.py')
state={'status':'RUNNING','private':str(w),'table_provider':str(B),'table_state_sha256':base_hash,'table_object_sha256':table_hash,'historical_object_sha256':historical_hash,'historical_state_sha256':hist_state_hash,'guards_sha256':bs['guards_sha256'],'providers_sha256':bs['providers_sha256'],'scope':'All non-private declarations attributed to historical WangTable, compared structurally by kernel type and universe parameters against the replacement and its chunk modules; historical object source provenance is not established. Attribute registration, definition values and canonical integration remain separate gates.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save(); print('PRIVATE',w,flush=True)
prefix='''import DiophantineConsistency.ArithmeticWangTable\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  for (n, idx) in env.const2ModIdx.toList do\n'''
checks={'historical':'(env.header.moduleNames).getD idx.toNat Name.anonymous == `DiophantineConsistency.ArithmeticWangTable','replacement':'(((env.header.moduleNames).getD idx.toNat Name.anonymous).toString.startsWith "DiophantineConsistency.ArithmeticWangTable")'}
paths={'historical':hs['LEAN_PATH'],'replacement':':'.join([str(B/'lib'),*bs['boundary']])}
try:
 for label in checks:
  s=w/(label+'.lean');s.write_text(prefix+f'    if {checks[label]} && !isPrivateName n then\n      if let some info := env.find? n then\n        logInfo m!"EXPORT {{n}} ::: {{reprStr info.type}} ::: {{reprStr info.levelParams}}"\n')
  log=w/(label+'.log');tim=w/(label+'.time');env=dict(os.environ,LEAN_PATH=paths[label],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
  cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',T,'-M6000','-j1','-DElab.async=false','-R',str(w),str(s)]
  print('START',label,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  state[label]={'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(s),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd};save();print('DONE',label,code,flush=True)
  if code:raise RuntimeError(label)
 def parse(p):
  s=p.read_text(); matches=list(re.finditer(r'^EXPORT (.*?) :::',s,re.M));assert matches and s.startswith('EXPORT ')
  d={}
  for i,m in enumerate(matches):
   n=m.group(1);assert n not in d;end=matches[i+1].start() if i+1<len(matches) else len(s);d[n]=s[m.end():end].strip()
  return d
 a=parse(w/'historical.log');b=parse(w/'replacement.log');missing=sorted(set(a)-set(b));diff=sorted(n for n in a.keys()&b.keys() if a[n]!=b[n]);extra=sorted(set(b)-set(a))
 result={'historical_count':len(a),'replacement_count':len(b),'missing':missing,'type_or_universe_mismatch':diff,'replacement_extra':extra,'historical_names':sorted(a)}
 (w/'comparison.json').write_text(json.dumps(result,indent=2)+'\n');state['comparison_sha256']=sha(w/'comparison.json');state['historical_count']=len(a);state['replacement_count']=len(b);state['missing_count']=len(missing);state['mismatch_count']=len(diff);assert auth();state['status']='PASS' if not missing and not diff else 'DIFFERENCES';save();print(state['status'],w,'missing',len(missing),'mismatch',len(diff),flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
