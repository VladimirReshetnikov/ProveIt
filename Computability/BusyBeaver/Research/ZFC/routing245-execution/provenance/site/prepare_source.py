"""Source-only245 site contracts at distance64; no checker or proof execution."""
import difflib,hashlib,json,pathlib,re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs'); B=pathlib.Path('/tmp/zfc-routing245-lean/site')
L=R/'Computability/BusyBeaver/Lean'; Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
sp0=L/'BusyBeaver/ZFC/SitePrefix246.lean'; ap0=Q/'prefix246_site_audit.lean'
assert sha(sp0)=='622c8b819df930b741a34c429b3911a1cc18e4a1e8f1582311e281fc24b844e2'
assert sha(ap0)=='54202e5803564eb4fb158e9c02b070532f20bd3a92ec7912da64f283da55ab67'
s0=sp0.read_text(); a0=ap0.read_text()
def rename(t):
 for a,b in [('SitePrefix246','SiteRouting245'),('SymbolicPrefix246','SymbolicRouting245'),('dispatchPrefix246','dispatchRouting245'),('machinePrefix246','machineRouting245')]:t=t.replace(a,b)
 return re.sub(r'\b246\b','245',t)
s=rename(s0).replace('def minDistance : Nat := 40','def minDistance : Nat := 64'); a=rename(a0)
a=a.replace('Q.length ≤ minDistance := checkSite_length Q e h','Q.length ≤ 64 := checkSite_length Q e h')
doc='''/-!
Per-instruction contracts for the literal routing245 machine at distance64.

Port of the checked SitePrefix246 contracts with the header margin changed
from40 to64 for the new decoder. Mira-Cult and Jeff's original Site.v proof
(upstream297ab8df7e5de329605c3875b4934643b371a5e3) and Wade's path semantics
retain their attribution. The physical register assignment is unchanged.
Permutation252Frame supplies only its layout functions here; its historical
40-distance frame predicate is not used by these site contracts.

The arbitrary gap parameter, overflow marker and extra-cell convention remain.
Positive decrement uses extra=1; every other operation uses extra=0. INC's
value-one spare and CD's following-block resource are in SymbolicRouting245.
Every binary step is justified by that executor and the exact routing245 table.

Fuel4000 remains the certificate-checker's limit pending measurement. It is
not a bound on concrete values or execution durations. Successful checks imply
positive whole-tape executions for every admitted gap and physical file.
The 8,391-case coverage, new distance64 frame, exact startup and PA endpoint
remain separate obligations.
-/'''
s=re.sub(r'/\-![\s\S]*?\-/',lambda _:doc,s,count=1)
strip=lambda t:re.sub(r'/\-[\s\S]*?\-/','',re.sub(r'--[^\n]*','',t))
assert strip(s.replace('def minDistance : Nat := 64','def minDistance : Nat := 40'))==strip(rename(s0))
assert strip(a.replace('Q.length ≤ 64 := checkSite_length Q e h','Q.length ≤ minDistance := checkSite_length Q e h'))==strip(rename(a0))
assert 'def fuel : Nat := 4000' in s
assert a.count('#print axioms ')==12 and a.count('\nexample ')==13
assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s)
sp=B/'SiteRouting245.lean'; ap=B/'Audit.lean'; assert not sp.exists() and not ap.exists(); sp.write_text(s); ap.write_text(a)
for label,x,y,p0,p1 in [('source',s0,s,sp0,sp),('audit',a0,a,ap0,ap)]:
 (B/f'{label}-from246.diff').write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=str(p0),tofile=str(p1))))
base=pathlib.Path('/tmp/zfc-routing245-lean/symbolic/boundary-plan.json'); bd=json.loads(base.read_text()); providers=bd['providers'].copy()
oldrecord=Q/'results/prefix246-site-verification.json'; d=json.loads(oldrecord.read_text()); assert d['status']=='PASS'
for name in ['BusyBeaver.ZFC.Table253','BusyBeaver.ZFC.RegisterBoxes253','BusyBeaver.ZFC.RegisterPath','BusyBeaver.ZFC.Permutation252Frame']:
 x=next(x for x in d['reused_modules'] if x['module']==name); source=L/pathlib.Path(name.replace('.','/')).with_suffix('.lean')
 assert sha(source)==x['source_sha256'] and sha(x['object'])==x['object_sha256']
 h=next(x for x in d['actual_first_providers'] if x['module']==name)
 assert h['sha256']==x['object_sha256'] and pathlib.Path(h['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
 providers.append(dict(x,source=str(source),selected_parent_record=desc(oldrecord)))
sym=pathlib.Path('/tmp/zfc-routing245-lean/symbolic/SymbolicRouting245.lean')
providers.append(dict(module='BusyBeaver.ZFC.SymbolicRouting245',source=str(sym),source_sha256=sha(sym),object=None,object_sha256=None,evidence=None,status='PENDING_ACTUAL_PASS'))
for x in providers:
 assert sha(x['source'])==x['source_sha256']
 if x['object'] is not None: assert sha(x['object'])==x['object_sha256']
seen=set(); external={'Init'}
def visit(name):
 if not name.startswith('BusyBeaver.'):external.add(name);return
 if name in seen:return
 seen.add(name); x=next(x for x in providers if x['module']==name)
 for dep in re.findall(r'^import ([A-Za-z0-9_.]+)$',pathlib.Path(x['source']).read_text(),re.M):visit(dep)
direct=re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)
for name in direct:visit(name)
assert len(seen)==17 and seen=={x['module'] for x in providers}
assert sum(x['object'] is not None for x in providers)==13
boundary=dict(status='SOURCE_ONLY_PENDING_NEW_EXECUTOR',source=desc(sp),audit=desc(ap),direct_imports=direct,expected_project_module_count=17,current_bound_provider_count=13,providers=providers,external_boundaries=sorted(external),toolchain_providers=d['toolchain_providers'],compiler=d['compiler'],named_probes=12,typed_callers=13,compiler_execution=False,guard_execution=False)
(B/'boundary-plan.json').write_text(json.dumps(boundary,indent=2)+'\n')
inv=dict(status='SOURCE_ONLY_NOT_COMPILED',source=desc(sp),audit=desc(ap),boundary=desc(B/'boundary-plan.json'),emitter=desc(pathlib.Path(__file__)),template_source=desc(sp0),template_audit=desc(ap0),semantic_changes=['minDistance40→64','Actual245 executor/table/state types','Audit bound caller explicitly specializes to64'],unchanged_checker_fuel=4000,positive_decrement_extra=1,all_other_extra=0,overflow_retained=True,arbitrary_gap_and_whole_tape=True,new_frame_definition_not_added=True,named_probes=12,typed_callers=13,expected_projects=17,current_bound_projects=13,pending_modules=[x['module'] for x in providers if x['object'] is None],default_limits=True,compiler_execution=False,guard_execution=False)
(B/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n'); print(json.dumps(inv,indent=2))
