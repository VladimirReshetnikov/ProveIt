"""Provisional direct-ordinate rebase with additive compatibility helpers over the historical 87 machine provider.

The full selected provider inventory is rehashed before and after. The 87 machine
provider and its inherited package/Foundation boundaries are *not* asserted to
be source-current; the outcome does not prove internal HA/PRA provability.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=R/'Computability/DiophantineConsistency/Lean';OLD=R/'Computability/DiophantineConsistency/research/wang-chunk-full/machine-rebase-current-orientation.lean';HELP=OLD.parent/'machine-rebase-compat-helpers-v8.lean';CURRENT=SRC/'DiophantineConsistency/AdaptiveDirectOrdinate86MainOrientation.lean';M=Path('/tmp/adaptive-unconditional-equivalence-ptaobui4');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ms=read(M/'state.json');bs=read(B/'state.json');FIRST=SRC/'DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean';MAIN=SRC/'DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean';CONG=SRC/'DiophantineConsistency/ArithmeticAdaptiveMainCongruence2011.lean';RCONG=SRC/'DiophantineConsistency/ArithmeticAdaptiveRankCongruence2011.lean';COMP=SRC/'DiophantineConsistency/ArithmeticAdaptiveIndexComparison2011.lean';STRONG=SRC/'DiophantineConsistency/ArithmeticAdaptiveStrongNorm2011.lean';comph=sha(COMP);strongh=sha(STRONG);firsth=sha(FIRST);mainh=sha(MAIN);congh=sha(CONG);rcongh=sha(RCONG);firsttext=FIRST.read_text();maintext=MAIN.read_text();pieces=[firsttext[firsttext.index('theorem mod_cancel'):firsttext.index('\ntheorem equivalent_mod')],firsttext[firsttext.index('theorem positive_Y_quotient_of_facts'):firsttext.index('\n/-- A literal positive zero',firsttext.index('theorem positive_Y_quotient_of_facts'))],maintext[maintext.index('theorem main_oriented_of_facts'):maintext.index('\n/-- An actual adaptive zero',maintext.index('theorem main_oriented_of_facts'))],CONG.read_text()[CONG.read_text().index('theorem main_congruence_of_facts'):CONG.read_text().index('\ntheorem expressionAt_main_congruence',CONG.read_text().index('theorem main_congruence_of_facts'))],RCONG.read_text()[RCONG.read_text().index('private theorem congruence_divides_difference'):RCONG.read_text().index('\ndef RankCongruence')],RCONG.read_text()[RCONG.read_text().index('theorem rank_congruence_of_main'):RCONG.read_text().index('\ntheorem expressionAt_rank_congruence',RCONG.read_text().index('theorem rank_congruence_of_main'))],COMP.read_text()[COMP.read_text().index('theorem two_le_of_positive_cube_quotient'):COMP.read_text().index('\ntheorem expressionAt_comparison',COMP.read_text().index('theorem two_le_of_positive_cube_quotient'))],STRONG.read_text()[STRONG.read_text().index('private theorem represented_unit'):STRONG.read_text().index('\ndef StrongNorm')],STRONG.read_text()[STRONG.read_text().index('theorem strong_norm_of_unit'):STRONG.read_text().index('\ntheorem expressionAt_strong_norm',STRONG.read_text().index('theorem strong_norm_of_unit'))]];assert all(HELP.read_text().count(x)==1 for x in pieces);assert ms['status']==bs['status']=='PASS';mh=sha(M/'state.json');bh=sha(B/'state.json');seen=set();build=[];boundary=[]
def source(n):
 return HELP if n=='DiophantineConsistency.AdaptiveDirectOrdinate86CompatHelpers' else OLD if n=='DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation' else SRC/('/'.join(n.split('.'))+'.lean')
def visit(n):
 if n in seen:return
 seen.add(n);obj=M/'lib'/('/'.join(n.split('.'))+'.olean')
 if obj.is_file():boundary.append(n);return
 p=source(n)
 if not p.is_file():boundary.append(n);return
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for x in line[7:].split():visit(x)
 build.append(n)
visit('DiophantineConsistency.AdaptiveDirectOrdinate86Machine');assert len(build)==27 and build[-1]=='DiophantineConsistency.AdaptiveDirectOrdinate86Machine';snap={n:sha(source(n)) for n in build};currenth=sha(CURRENT);assert OLD.read_text()=='import DiophantineConsistency.AdaptiveDirectOrdinate86CompatHelpers\n'+CURRENT.read_text()
# Walk directory symlinks as well; record resolved selected objects, not just leaf overlays.
providers={}
for root,dirs,files in os.walk(M/'lib',followlinks=True):
 for f in files:
  p=Path(root)/f
  if f.endswith('.olean'):
   key=str(p.relative_to(M/'lib'));providers[key]={'path':str(p.resolve()),'sha256':sha(p)}
assert len(providers)==507
for n in boundary:
 key='/'.join(n.split('.'))+'.olean'
 if n.startswith('DiophantineConsistency.'):assert key in providers, n
w=Path(tempfile.mkdtemp(prefix='adaptive86-machine-compat-rebase-v9-'));(w/'logs').mkdir();lib=w/'lib';shutil.copyfile(__file__,w/'driver.py');(w/'providers.json').write_text(json.dumps(providers,indent=2,sort_keys=True)+'\n');ph=sha(w/'providers.json')
for n in build:
 p=source(n);q=w/'logs'/(n.split('.')[-1]+'.lean');shutil.copyfile(p,q)
for root,dirs,files in os.walk(M/'lib',followlinks=True):
 for f in files:
  p=Path(root)/f;dst=lib/p.relative_to(M/'lib');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(p.resolve())
state={'status':'RUNNING','private':str(w),'machine_state_sha256':mh,'boundary_state_sha256':bh,'provider_inventory_sha256':ph,'selected_provider_count':len(providers),'build_order':build,'direct_boundaries':boundary,'source_sha256':snap,'augmented_orientation_source':str(OLD),'current_orientation_source_sha256':currenth,'compat_helper_source':str(HELP),'first_divisibility_source_sha256':firsth,'main_orientation_source_sha256':mainh,'main_congruence_source_sha256':congh,'rank_congruence_source_sha256':rcongh,'index_comparison_source_sha256':comph,'strong_norm_source_sha256':strongh,'records':[],'scope':'Provisional 27-module 86 rebase on the independently replayed historical 87 provider, with eight public helper declarations and their private proof support and the exact current 86 MainOrientation source preceded by a private compatibility import; complete selected object bytes reauthenticated, inherited project/package/Foundation source boundaries remain historical; no complete current-source closure or HA/PRA provability claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
def auth():
 return sha(M/'state.json')==mh and sha(B/'state.json')==bh and sha(FIRST)==firsth and sha(MAIN)==mainh and sha(CONG)==congh and sha(RCONG)==rcongh and sha(COMP)==comph and sha(STRONG)==strongh and all(HELP.read_text().count(x)==1 for x in pieces) and sha(CURRENT)==currenth and OLD.read_text()=='import DiophantineConsistency.AdaptiveDirectOrdinate86CompatHelpers\n'+CURRENT.read_text() and sha(w/'providers.json')==ph and all(sha(source(n))==h for n,h in snap.items()) and all(sha(x['path'])==x['sha256'] for x in providers.values())
save();print('PRIVATE',w,'MODULES',len(build),'PROVIDERS',len(providers),flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in build:
  short=n.split('.')[-1];src=source(n);out=lib/('/'.join(n.split('.'))+'.olean');log=w/'logs'/(short+'.log');tim=w/'logs'/(short+'.time');assert not out.exists() and sha(src)==snap[n];cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',short,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',short,code,flush=True)
  if code:raise RuntimeError(n)
 assert auth() and all(sha(w/'logs'/(r['name'].split('.')[-1]+'.lean'))==r['source_sha256'] and sha(lib/('/'.join(r['name'].split('.'))+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.time'))==r['time_sha256'] for r in state['records']);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
