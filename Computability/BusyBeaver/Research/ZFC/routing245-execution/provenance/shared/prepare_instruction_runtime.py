"""Source-only instruction/runtime ports with explicit coverage and frame64."""
import difflib, hashlib, json, pathlib, re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs'); B=pathlib.Path('/tmp/zfc-routing245-lean')
L=R/'Computability/BusyBeaver/Lean'; Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
strip=lambda t:re.sub(r'/\-[\s\S]*?\-/','',re.sub(r'--[^\n]*','',t))
def rename(t):
 for a,b in [('RuntimeInstancePrefix246','RuntimeInstanceRouting245'),('InstructionPrefix246','InstructionRouting245'),('Prefix246Simulation','Routing245Simulation'),('SitePrefix246','SiteRouting245'),('SymbolicPrefix246','SymbolicRouting245'),('machinePrefix246','machineRouting245'),('DispatchFrame','DispatchFrame64')]:t=t.replace(a,b)
 return re.sub(r'\b40\b','64',re.sub(r'\b246\b','245',t))
specs=[
 dict(lane='instruction',old='InstructionPrefix246',new='InstructionRouting245',prefix='instruction',source_sha='ec777c8cf810999e4e1b69b3a9adec8ba66e014c218d03c74bc654d9f1cc86dd',audit_sha='4d2544d4a4238fb292346a2b654e3b6381faf1313aab888c8fa8e06ab1eedd57',probes=7,callers=7,projects=22,bound=16,
 doc='''/-!
One complete logical instruction of the routing245 machine.

This composes the actual site checker with the scoped DispatchFrame64
adapters. Mira-Cult and Jeff's original machine verification and Wade's path
semantics retain the attribution given in SiteRouting245.

Every accepted nonhalting site implements the logical step with a strictly
positive number of actual binary moves, preserves a nonempty spare suffix,
and returns the whole infinite tape in a 64-cell dispatch frame. Increment
appends a value-one spare; positive decrement preserves the suffix and adds
one gap cell. Register values, gap parameters and spare values are arbitrary.
The accepted-site premise is explicit; full decoder coverage is separate.
-/'''),
 dict(lane='runtime',old='RuntimeInstancePrefix246',new='RuntimeInstanceRouting245',prefix='runtime',source_sha='f698845e32f546f4937a6d5ae819dd16c0975280c7b6f470f27ddb593ffa7bdb',audit_sha='a421611e674ddc0bed525317634fdf1566a091737f9b22e9dfd561a12cc4d8c4',probes=11,callers=12,projects=26,bound=19,
 doc='''/-!
Whole-frame routing245 runtime equivalence, conditional on exact site coverage.

Port of RuntimeInstancePrefix246 using the unchanged RuntimePerm252 positive
simulation theorem and Mira-Cult, Jeff and Wade's attributed framework.
Related retains the clean instruction pointer, the entire DispatchFrame64
and a nonempty finite spare suffix. The instruction adapter preserves that
resource: increment appends [1], while other operations preserve the suffix.
Positive decrement and instruction-pointer overflow can increase the gap.

Covered remains an explicit premise for an arbitrary register program. It
supplies successful decoding and each accepted concrete site, including the
identification of a failed logical step with an actual halt leaf. Both halting
directions follow from positive full-tape segments, with no bound on register
values or total execution time. The allSites client still requires the exact
whole-tree certificate. Actual coverage, blank startup and PA comparison
are not discharged by this module.
-/''')]
base=json.loads((B/'frame/boundary-plan.json').read_text())
providers=base['providers'].copy()
frame=B/'frame/Routing245Simulation.lean'
providers.append(dict(module='BusyBeaver.ZFC.Routing245Simulation',source=str(frame),source_sha256=sha(frame),object=None,object_sha256=None,evidence=None,status='OBJECT_NOT_SELECTED_IN_SOURCE_PLAN'))
for spec in specs:
 D=B/spec['lane']; sp0=L/f'BusyBeaver/ZFC/{spec["old"]}.lean'; ap0=Q/f'prefix246_{spec["prefix"]}_audit.lean'
 assert sha(sp0)==spec['source_sha'] and sha(ap0)==spec['audit_sha']
 s0,a0=sp0.read_text(),ap0.read_text();s=rename(s0);a=rename(a0)
 s=re.sub(r'/\-![\s\S]*?\-/',lambda _:spec['doc'],s,count=1)
 # DispatchFrame64 belongs to the new scoped Simulation namespace, whereas
 # the old audit obtained DispatchFrame from its opened generic Frame module.
 marker='open RegisterPath '
 idx=a.index(marker)
 a=a[:idx]+'open Routing245Simulation\n'+a[idx:]
 assert strip(s)==strip(rename(s0))
 assert strip(a.replace('open Routing245Simulation\n','',1))==strip(rename(a0))
 assert not re.search(r'\b(?:40|246|DispatchFrame)\b',strip(s)+'\n'+strip(a))
 assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',strip(s))
 assert a.count('#print axioms ')==spec['probes'] and a.count('\nexample ')==spec['callers']
 sp,ap=D/f'{spec["new"]}.lean',D/'Audit.lean';assert not sp.exists() and not ap.exists()
 sp.write_text(s);ap.write_text(a)
 for label,x,y,p0,p1 in [('source',s0,s,sp0,sp),('audit',a0,a,ap0,ap)]:
  (D/f'{label}-from246.diff').write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=str(p0),tofile=str(p1))))
 oldrecord=Q/f'results/prefix246-{spec["prefix"]}-verification.json';d=json.loads(oldrecord.read_text());assert d['status']=='PASS'
 if spec['lane']=='runtime':
  for name in ['BusyBeaver.ZFC.RuntimePerm252','BusyBeaver.ZFC.RMBisim','BusyBeaver.ZFC.SiteCoverage']:
   x=next(x for x in d['reused_modules'] if x['module']==name);source=L/pathlib.Path(name.replace('.','/')).with_suffix('.lean')
   assert sha(source)==x['source_sha256'] and sha(x['object'])==x['object_sha256']
   p=next(x for x in d['actual_first_providers'] if x['module']==name)
   assert p['sha256']==x['object_sha256'] and pathlib.Path(p['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
   providers.append(dict(x,source=str(source),selected_parent_record=desc(oldrecord)))
 for x in providers:
  assert sha(x['source'])==x['source_sha256']
  if x['object'] is not None:assert sha(x['object'])==x['object_sha256']
 seen=set();external={'Init'}
 def visit(name):
  if not name.startswith('BusyBeaver.'):external.add(name);return
  if name in seen:return
  seen.add(name);x=next(x for x in providers if x['module']==name)
  for dep in re.findall(r'^import ([A-Za-z0-9_.]+)$',pathlib.Path(x['source']).read_text(),re.M):visit(dep)
 direct=re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)
 for name in direct:visit(name)
 assert len(seen)==spec['projects'] and seen=={x['module'] for x in providers}
 assert sum(x['object'] is not None for x in providers)==spec['bound']
 bd=dict(status='SOURCE_ONLY_PROSPECTIVE_PROVIDER_PLAN',source=desc(sp),audit=desc(ap),direct_imports=direct,
         expected_project_module_count=spec['projects'],current_bound_provider_count=spec['bound'],providers=providers.copy(),
         external_boundaries=sorted(external),toolchain_providers=d['toolchain_providers'],compiler=d['compiler'],
         named_probes=spec['probes'],typed_callers=spec['callers'],compiler_execution=False,guard_execution=False,
         unselected_new_provider_policy='Null object fields mean not yet selected for this source plan; they do not assert no actual PASS exists elsewhere.')
 (D/'boundary-plan.json').write_text(json.dumps(bd,indent=2)+'\n')
 inv=dict(status='SOURCE_ONLY_NOT_COMPILED',source=desc(sp),audit=desc(ap),boundary=desc(D/'boundary-plan.json'),emitter=desc(pathlib.Path(__file__)),
          template_source=desc(sp0),template_audit=desc(ap0),template_record=desc(oldrecord),
          semantic_changes=['New scoped DispatchFrame64 throughout','Every old margin/gap40 replaced coherently by64','Actual245 machine/site/state types'],
          normalized_proof_bodies_equal=True,positive_segments=True,whole_tape=True,arbitrary_registers_gaps_spares=True,
          accepted_sites_explicit=True,covered_explicit=(spec['lane']=='runtime'),coverage_proved=False,bootstrap_proved=False,
          named_probes=spec['probes'],typed_callers=spec['callers'],expected_projects=spec['projects'],current_bound_projects=spec['bound'],
          unselected_modules=[x['module'] for x in providers if x['object'] is None],default_proof_limits=True,compiler_execution=False,guard_execution=False)
 (D/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
 print(json.dumps({k:inv[k] for k in ['status','source','audit','boundary','named_probes','typed_callers','expected_projects','current_bound_projects']},indent=2))
 providers.append(dict(module='BusyBeaver.ZFC.'+spec['new'],source=str(sp),source_sha256=sha(sp),object=None,object_sha256=None,evidence=None,status='OBJECT_NOT_SELECTED_IN_SOURCE_PLAN'))
