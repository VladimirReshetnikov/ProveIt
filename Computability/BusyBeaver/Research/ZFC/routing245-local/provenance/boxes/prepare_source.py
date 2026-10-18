"""Source-only245 box port; unknown Pulse proof object remains explicitly pending."""
import ast,difflib,hashlib,json,pathlib,re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs');B=pathlib.Path('/tmp/zfc-routing245-lean/boxes')
L=R/'Computability/BusyBeaver/Lean';Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
sp0=L/'BusyBeaver/ZFC/Prefix246Boxes.lean';ap0=Q/'prefix246_boxes_audit.lean'
assert sha(sp0)=='af1070a0840f4bcf05ffadef7042b246a6a9022d8acc770f33b58c5e5e51ee54'
assert sha(ap0)=='38408d5b15c449603b582a28af7491706e26221b3d565a1525d1143451a1cea3'
s0=sp0.read_text();a0=ap0.read_text()
def rename(s):
 return s.replace('Prefix246Boxes','Routing245Boxes').replace('Prefix246Pulse','Routing245Pulse').replace('machinePrefix246','machineRouting245').replace('oldStatePrefix246','oldStateRouting245').replace('rowPrefix246','rowRouting245').replace('Fin 246','Fin 245').replace('Config 246','Config 245')
s=rename(s0);a=rename(a0)
doc='''/-!
Unbounded unary-register excursions of the exact routing245 table.

Direct port of the checked Prefix246Boxes proofs. The old-label arithmetic
rows are unchanged in source 68 (arrival 8286787dd0468d848db345debe304b002d7064a4).
Every step uses the new literal table and the Routing245Pulse local lemma.
The generic list encoding and table-parametric return scanner are reused
from RegisterBoxesPerm252/RegisterMarkPerm252; no 252 execution theorem is used.

Source 63 supplies the contextual pulse fold; the shared-carry macros came
from source 58 (arrival 126d12e470). Mira-Cult's original binary machine,
Jeff's verification, and Wade's compiler framework retain their attribution.

All natural register values, arbitrary finite left context, and the complete
zero-exterior tape are covered. INC appends one value-one spare; positive CD
moves the boundary one cell right; zero CD requires an actual following block.
No blank bootstrap, all-sites acceptance or consistency endpoint is asserted.
-/'''
s=re.sub(r'/\-![\s\S]*?\-/',lambda _:doc,s,count=1)
# Correct only inherited prose after exact identifier/state substitution.
s=s.replace('three literal246 rows','three literal245 rows')
a=a.replace('exact final246 state map','exact routing245 state map')
strip=lambda t:re.sub(r'/\*[\s\S]*?\*/','',re.sub(r'/\-[\s\S]*?\-/','',re.sub(r'--[^\n]*','',t)))
assert strip(s)==strip(rename(s0));assert strip(a)==strip(rename(a0))
assert a.count('#print axioms ')==14 and a.count('\nexample ')==19
assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s)
sp=B/'Routing245Boxes.lean';ap=B/'Audit.lean';assert not sp.exists()and not ap.exists();sp.write_text(s);ap.write_text(a)
for label,x,y,p0,p1 in [('source',s0,s,sp0,sp),('audit',a0,a,ap0,ap)]:
 (B/f'{label}-from246.diff').write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=str(p0),tofile=str(p1))))
oldrecord=Q/'results/prefix246-boxes-verification.json';assert sha(oldrecord)=='bd0671838ff39bbc6d3009c420858747b868988e17fe41b32e8e88ba8db8974a'
d=json.loads(oldrecord.read_text());assert d['status']=='PASS'
markboundary=json.loads(pathlib.Path('/tmp/zfc-routing245-lean/mark/boundary.json').read_text())
providers=[]
for x in markboundary['providers']:
 x=dict(x)
 if x['module']!='BusyBeaver.ZFC.TableRouting245':
  old=next(v for v in d['reused_modules']if v['module']==x['module'])
  assert old['source_sha256']==x['source_sha256']and old['object_sha256']==x['object_sha256']
  h=next(v for v in d['actual_first_providers']if v['module']==x['module'])
  assert h['sha256']==x['object_sha256']and pathlib.Path(h['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
  x['selected_parent_record']=desc(oldrecord)
 assert sha(x['source'])==x['source_sha256']and sha(x['object'])==x['object_sha256']
 providers.append(x)
pulse=pathlib.Path('/tmp/zfc-routing245-lean/pulse/Routing245Pulse.lean');assert sha(pulse)=='57465a4b514feca33a1b1148a3bf51ae92462f97a6f965ad0e1b8dcb53ab2685'
pending=dict(module='BusyBeaver.ZFC.Routing245Pulse',source=str(pulse),source_sha256=sha(pulse),status='PENDING_ACTUAL_PASS',object=None,object_sha256=None,evidence=None)
allproviders=providers+[pending];seen=set();external={'Init'}
def visit(name):
 if not name.startswith('BusyBeaver.'):external.add(name);return
 if name in seen:return
 seen.add(name);x=next(x for x in allproviders if x['module']==name)
 for dep in re.findall(r'^import ([A-Za-z0-9_.]+)$',pathlib.Path(x['source']).read_text(),re.M):visit(dep)
for name in ['BusyBeaver.ZFC.Routing245Pulse','BusyBeaver.ZFC.RegisterMarkPerm252']:visit(name)
assert len(seen)==8and seen=={x['module']for x in allproviders}
boundary=dict(status='SOURCE_ONLY_PENDING_PULSE_PASS',source=desc(sp),audit=desc(ap),direct_imports=['BusyBeaver.ZFC.Routing245Pulse','BusyBeaver.ZFC.RegisterMarkPerm252'],expected_project_module_count=8,current_bound_provider_count=7,providers=allproviders,external_boundaries=sorted(external),toolchain_providers=d['toolchain_providers'],compiler=d['compiler'],required_fresh_parent='BusyBeaver.ZFC.Routing245Pulse',named_probes=14,typed_callers=19,compiler_execution=False,guard_execution=False)
(B/'boundary-plan.json').write_text(json.dumps(boundary,indent=2)+'\n')
# Same established CLI, policy and execution body; only future Pulse evidence pin is absent.
gp=pathlib.Path('/tmp/zfc-prefix246-lean/boxes/check.py');g0=gp.read_text();g=g0
for x,y in [('exact246','exact245'),('Prefix246Boxes','Routing245Boxes'),('Prefix246Pulse','Routing245Pulse'),('TablePrefix246','TableRouting245'),('/tmp/zfc-prefix246-lean/boxes/','/tmp/zfc-routing245-lean/boxes/'),('af1070a0840f4bcf05ffadef7042b246a6a9022d8acc770f33b58c5e5e51ee54',sha(sp)),('38408d5b15c449603b582a28af7491706e26221b3d565a1525d1143451a1cea3',sha(ap)),('a51632e7a25ba048d8a988a07546637a8937649aec48303d167886f6b16b69e1','PENDING_SUCCESSFUL_PULSE_RECORD'),('92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b',sha(oldrecord)),('MP_RECORD_SHA','BOXES_RECORD_SHA'),('arithmetic-control-mp254-verification.json','prefix246-boxes-verification.json')]:g=g.replace(x,y)
g=re.sub(r'\bMP\b','BOXES',g);g=re.sub(r'\bmp\b','boxes',g)
needle="    assert [q['label'] for q in d['commands']] == ['source', 'audit']\n";g=g.replace(needle,needle+"    assert d['before'] == d['after']\n    assert d['source_object_recorded_before_audit']\n")
needle="    assert q['object_sha256'] == object_sha == sha(obj)\n";g=g.replace(needle,needle+"    historical = next(x for x in boxes['actual_first_providers'] if x['module'] == m)\n    assert historical['sha256'] == object_sha\n    assert Path(historical['actual_first']).resolve() == obj\n")
needle="assert parent['source_pass_object'] == q\n";g=g.replace(needle,needle+"assert parent['fresh_first_provider_before_audit']['sha256'] == q['sha256']\nassert Path(parent['fresh_first_provider_before_audit']['path']).resolve() == pulse_object\n")
g=g.replace("tools = []\n","assert tool_names == {'Init', 'Lean.Elab.Tactic.Omega'}\ntool_pins = {q['module']: q['object_sha256'] for q in boxes['toolchain_providers']}\ntools = []\n")
g=g.replace("    assert obj.resolve() == ref.resolve()\n","    assert obj.resolve() == ref.resolve()\n    assert sha(obj) == tool_pins[m]\n")
assert g[g.index('deadline = time.monotonic() + TIMEOUT'):]==g0[g0.index('deadline = time.monotonic() + TIMEOUT'):]
ast.parse(g);check=B/'check.py';assert not check.exists();check.write_text(g)
(B/'guard-from246.diff').write_text(''.join(difflib.unified_diff(g0.splitlines(True),g.splitlines(True),fromfile=str(gp),tofile=str(check))))
inv=dict(status='SOURCE_ONLY_PENDING_PULSE_PASS',source=desc(sp),audit=desc(ap),boundary=desc(B/'boundary-plan.json'),guard=desc(check),emitter=desc(pathlib.Path(__file__)),template_source=desc(sp0),template_audit=desc(ap0),guard_template=desc(gp),proof_bodies_exact_after_renaming=True,proof_execution_body_unchanged=True,named_probes=14,typed_callers=19,expected_projects=8,current_bound_projects=7,missing_parent='Routing245Pulse actualPASS',shared_seconds=120,flags=['-j1','-M4096'],default_limits=True,compiler_execution=False,guard_execution=False)
(B/'source-guard-inventory.json').write_text(json.dumps(inv,indent=2)+'\n');print(json.dumps(inv,indent=2))
