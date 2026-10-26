from pathlib import Path
import json,hashlib,re,collections,subprocess
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';rev=d/'reviews';leaf=d/'Lean/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
planfile=rev/'ha-native-merge-refresh-20261026/plan.json';statefile=planfile.with_name('state.json');base=json.loads(planfile.read_text());state=json.loads(statefile.read_text());require(state['status']=='PASS','Base incomplete');require(sha(planfile)==state['plan_sha256'],'Base pin')
# Remove comments/strings before scanning actual imports, including nested Lean comments.
def strip(s):
 out=[];i=0;depth=0;line=False;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif line:
   if s[i]=='\n':line=False;out.append('\n')
   i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):line=True;i+=2
  elif s[i]=='"':string=True;i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
def imports(p):return re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',strip(Path(p).read_text()),re.M)
mods={m['module']:dict(m) for m in base['modules']}
for done in state['completed']:
 if done['module'] in mods:mods[done['module']]['object']=done['object']
newdata=['LowMaskData','WangTiles942TableData','CurrentMaskData2011','CurrentKernelData2011','CurrentEquationSyntax2011'];newclients=['NearSquareNormZero','NearSquareNormZeroChecks','CarrierNonzeroSpheres','CarrierNonzeroSpheresChecks']
for name in newdata+newclients:
 full='DiophantineConsistency.'+name;p=leaf/(name+'.lean');require(full not in mods,'Already inbase');mods[full]=dict(module=full,source=dict(path=str(p),sha256=sha(p)),origin='new-data'if name in newdata else'new-sphere')
changed=[]
for n,m in mods.items():
 p=Path(m['source']['path']);actual=sha(p)
 if actual!=m['source']['sha256']:changed.append(n)
 m['prior_source_sha256']=m['source']['sha256'];m['source']=dict(path=str(p),sha256=actual);m['imports']=imports(p)
 if 'object'in m:require(sha(m['object']['path'])==m['object']['sha256'],'Object drift '+n)
expected=['LowMaskCoding','WangTiles942Core','CurrentMasks2011','CurrentKernel2011','CurrentWindowCarry2011','ObjectCurrentEquation2011','ArithmeticCurrentEquation2011']
require(set(changed)=={'DiophantineConsistency.'+n for n in expected},'Unexpected source drift '+str(changed))
seed=set(changed)|{'DiophantineConsistency.'+n for n in newdata+newclients}
affected=set(seed)
while True:
 more={n for n,m in mods.items() if any(i in affected for i in m['imports'])};new=affected|more
 if new==affected:break
 affected=new
# All requested actual clients already present in469, plus new sphere pair.
targetnames=expected+['CurrentPositiveZero2011Checks','CurrentWitnessEquivalence2011Checks','ThirteenLVCarrierChecks','ThirteenGroupedSquares96Checks','ThirteenSharedSquares96Checks','ThirteenUnitSphere96Checks','CarrierScaledAuxiliary118Checks','HAEquationStability2011Checks','ArithmeticExpressionChecks']+newclients
roots={'DiophantineConsistency.'+n for n in targetnames};require(roots<=mods.keys(),'Target outsideinventory')
needed=set()
def visit(n):
 if n in needed:return
 needed.add(n)
 for i in mods[n]['imports']:
  if i in mods:visit(i)
for n in sorted(roots):visit(n)
fresh=affected&needed
# Dependency-ordered list, with no reused node importing a fresh node.
ordered=[];visiting=set();done=set()
def topo(n):
 if n in done:return
 require(n not in visiting,'Cycle '+n);visiting.add(n)
 for i in mods[n]['imports']:
  if i in needed:topo(i)
 visiting.remove(n);done.add(n);ordered.append(n)
for n in sorted(needed):topo(n)
boundary=[dict(module=n,fresh_imports=[i for i in mods[n]['imports'] if i in fresh]) for n in needed-fresh if any(i in fresh for i in mods[n]['imports'])]
require(not boundary,'Stale reusedclient edge')
for n,m in mods.items():m['planned_action']='fresh'if n in fresh else'reuse'if n in needed else'outside-minimal-request';m['affected']=n in affected
out=dict(status='READ_ONLY_PLAN_NOT_EXECUTED',snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),scope='Accepted469 plus five narrow data owners and four new spheres leaves. Actual Foundation binding is separately fresh; no Foundation/umbrella rebuild. Every changed dependency descendant needed by requested clients is fresh.',parent_plan=dict(path=str(planfile),sha256=sha(planfile)),parent_state=dict(path=str(statefile),sha256=sha(statefile)),counts=dict(inventory=len(mods),changed_existing=len(changed),new_data=len(newdata),new_sphere=len(newclients),all_affected=len(affected),needed=len(needed),fresh=len(fresh),reused=len(needed-fresh),outside=len(set(mods)-needed)),roots=sorted(roots),changed=sorted(changed),fresh_dependency_order=[n for n in ordered if n in fresh],reuse_dependency_order=[n for n in ordered if n not in fresh],reused_clients_importing_fresh=boundary,modules=[mods[n] for n in ordered]+[mods[n] for n in sorted(set(mods)-needed)],driver_sha256=sha(__file__))
path=rev/'current-equation-narrow-native-plan.json';path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['counts'],indent=2));print('FRESH');print('\n'.join(out['fresh_dependency_order']));print('OUTSIDE',sorted(set(mods)-needed));print('HASH',sha(path))
