"""Emit only source/audit for the exact245 symbolic executor; never run proofs."""
import difflib,hashlib,json,pathlib,re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs'); B=pathlib.Path('/tmp/zfc-routing245-lean/symbolic')
L=R/'Computability/BusyBeaver/Lean'; Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
sp0=L/'BusyBeaver/ZFC/SymbolicPrefix246.lean'; ap0=Q/'prefix246_symbolic_audit.lean'
assert sha(sp0)=='aea11cb4168669f53a11a212ab1834d4725624919b0d4d047b125fc730349aec'
assert sha(ap0)=='4db44c5cda6d94c2221a174cc506a3094ec1ca20f9b72548b6c05d5ec1a5d80d'
s0=sp0.read_text(); a0=ap0.read_text()
changes=[('SymbolicPrefix246','SymbolicRouting245'),('Prefix246Boxes','Routing245Boxes'),('RegisterMarkPrefix246','RegisterMarkRouting245'),('FastTablePrefix246','FastTableRouting245'),('machinePrefix246','machineRouting245')]
def rename(t):
 for a,b in changes:t=t.replace(a,b)
 return re.sub(r'\b246\b','245',t)
s=rename(s0); a=rename(a0)
doc='''/-!
Sound affine symbolic execution for the exact routing245 table.

Direct port of the checked SymbolicPrefix246 proof, retaining the attributed
Mira-Cult/Jeff/Wade framework, source 58's shared carry and source 63's
contextual folds. Source 68 changes the literal decoder table; every literal
transition here uses the independently checked FastTableRouting245 lookup.
There is no whole-table renaming assumption.

The nine selector entries are regenerated from exact routing245 numbering.
Their soundness and completeness are checked against RegisterMarkRouting245.
Only original labels used by the new local Boxes/Mark proofs are reused;
missing old247 is never interpreted through the total state-map fallback.

Valid files have nine primaries and a nonempty finite spare suffix. Increment
appends one value-one spare; positive decrement shifts the file boundary
right one; zero decrement requires a following block and returns via old112.
Whole-tape denotation, arbitrary gaps and values, positive literal-progress
witnesses, normalization soundness and the actual final halt action remain.

The executor soundness depends on the new literal table, local box and mark
parents. All-site acceptance, exact startup, and the PA endpoint are separate.
-/'''
s=re.sub(r'/\-![\s\S]*?\-/',lambda _:doc,s,count=1)
s=s.replace('after exact246 renumbering','after exact routing245 renumbering')
# Regenerate the finite selector recognizer from the plain candidate map.
mp=Q/'candidate-routing245/renumbering.json'; mapping=json.loads(mp.read_text())['old_to_canonical']
labels=[60,44,31,56,38,40,28,64,69]; numbers=[mapping[str(x)] for x in labels]
expected=[54,39,27,51,34,36,24,58,63]; assert numbers==expected
block='def skipTarget (q : Fin 245) : Option Reg :=\n  match q.val with\n'+''.join(f'  | {q} => some ⟨{i}, by decide⟩\n' for i,q in enumerate(numbers))+'  | _ => none'
s,n=re.subn(r'def skipTarget \(q : Fin 245\) : Option Reg :=\n  match q.val with\n(?:  \|[^\n]*\n)*  \| _ => none',lambda _:block,s,count=1); assert n==1
# The newly generated finite cases are equal to the old numeric cases; all logical bodies stay exact.
def without_comments(t):
 return re.sub(r'/\-[\s\S]*?\-/','',re.sub(r'--[^\n]*','',t))
assert without_comments(s)==without_comments(rename(s0))
assert without_comments(a)==without_comments(rename(a0))
assert a.count('#print axioms ')==15 and a.count('\nexample ')==15
assert '10 ≤ vs.length ∧ match br with' in s
assert s.count('FastTableRouting245.fastMachine.transition')==4
assert s.count('FastTableRouting245.fast_transition_eq')==5
assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s)
sp=B/'SymbolicRouting245.lean'; ap=B/'Audit.lean'; assert not sp.exists() and not ap.exists()
sp.write_text(s); ap.write_text(a)
for label,x,y,p0,p1 in [('source',s0,s,sp0,sp),('audit',a0,a,ap0,ap)]:
 (B/f'{label}-from246.diff').write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=str(p0),tofile=str(p1))))
oldrecord=Q/'results/prefix246-symbolic-verification.json'; d=json.loads(oldrecord.read_text()); assert d['status']=='PASS'
generic=['BusyBeaver.Core','BusyBeaver.ZFC.FiniteZipper','BusyBeaver.ZFC.ZipperRuns','BusyBeaver.ZFC.TablePerm252','BusyBeaver.ZFC.RegisterBoxesPerm252','BusyBeaver.ZFC.RegisterMarkPerm252','BusyBeaver.ZFC.WritingRuns']
providers=[]
for name in generic:
 x=next(x for x in d['reused_modules'] if x['module']==name); source=L/pathlib.Path(name.replace('.','/')).with_suffix('.lean')
 assert sha(source)==x['source_sha256'] and sha(x['object'])==x['object_sha256']
 h=next(x for x in d['actual_first_providers'] if x['module']==name)
 assert h['sha256']==x['object_sha256'] and pathlib.Path(h['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
 providers.append(dict(x,source=str(source),selected_parent_record=desc(oldrecord)))
for name,file in [('TableRouting245','table-routing245'),('FastTableRouting245','fast-table-routing245')]:
 ep=Q/'results'/f'{file}-verification.json'; e=json.loads(ep.read_text()); assert e['status']=='PASS'
 f=next(x for x in e['fresh_modules'] if x['module']=='BusyBeaver.ZFC.'+name); source=L/'BusyBeaver/ZFC'/f'{name}.lean'
 assert sha(source)==f['source_sha256'] and sha(f['path'])==f['sha256']
 assert e['source_pass_object']['sha256']==f['sha256']
 providers.append(dict(module=f['module'],source=str(source),source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'],selected_parent_record=desc(ep)))
for name,lane in [('Routing245Pulse','pulse'),('Routing245Boxes','boxes'),('RegisterMarkRouting245','mark')]:
 source=pathlib.Path('/tmp/zfc-routing245-lean')/lane/f'{name}.lean'
 providers.append(dict(module='BusyBeaver.ZFC.'+name,source=str(source),source_sha256=sha(source),object=None,object_sha256=None,evidence=None,status='PENDING_ACTUAL_PASS'))
seen=set(); external={'Init'}
def visit(name):
 if not name.startswith('BusyBeaver.'):external.add(name);return
 if name in seen:return
 seen.add(name); x=next(x for x in providers if x['module']==name)
 for dep in re.findall(r'^import ([A-Za-z0-9_.]+)$',pathlib.Path(x['source']).read_text(),re.M):visit(dep)
direct=re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)
for name in direct:visit(name)
assert len(seen)==12 and seen=={x['module'] for x in providers}
assert sum(x.get('object') is not None for x in providers)==9
boundary=dict(status='SOURCE_ONLY_PENDING_NEW_LOCAL_PARENTS',source=desc(sp),audit=desc(ap),direct_imports=direct,expected_project_module_count=12,current_bound_provider_count=9,providers=providers,external_boundaries=sorted(external),toolchain_providers=d['toolchain_providers'],compiler=d['compiler'],named_probes=15,typed_callers=15,compiler_execution=False,guard_execution=False)
(B/'boundary-plan.json').write_text(json.dumps(boundary,indent=2)+'\n')
inv=dict(status='SOURCE_ONLY_NOT_COMPILED',source=desc(sp),audit=desc(ap),boundary=desc(B/'boundary-plan.json'),emitter=desc(pathlib.Path(__file__)),template_source=desc(sp0),template_audit=desc(ap0),candidate_map=desc(mp),selectors=[dict(physical_register=i,old_label=old,canonical=q) for i,(old,q) in enumerate(zip(labels,numbers))],proof_bodies_exact_after_renaming=True,named_probes=15,typed_callers=15,whole_tape_preserved=True,valid_min_blocks=10,positive_progress_and_halt_preserved=True,new_fast_table_binding=True,expected_projects=12,current_bound_projects=9,pending_modules=['Routing245Pulse','Routing245Boxes','RegisterMarkRouting245'],default_limits=True,compiler_execution=False,guard_execution=False)
(B/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n'); print(json.dumps(inv,indent=2))
