"""Source-only exact245 marking port and bounded guard; no proof invocation."""
import ast,difflib,hashlib,json,pathlib,re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs');B=pathlib.Path('/tmp/zfc-routing245-lean/mark')
L=R/'Computability/BusyBeaver/Lean';Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
sp0=L/'BusyBeaver/ZFC/RegisterMarkPrefix246.lean';ap0=Q/'prefix246_mark_audit.lean'
assert sha(sp0)=='a3d3f96a91838f67ab78b1732e18d6cefc7dc0e863af6556681f64cab2d3c809'
assert sha(ap0)=='47f53ff307261f48f4fb35bd0d115520c03451791085eb7c8726d818717f5443'
s0=sp0.read_text();a0=ap0.read_text()
def rename(s):
 return s.replace('RegisterMarkPrefix246','RegisterMarkRouting245').replace('TablePrefix246','TableRouting245').replace('machinePrefix246','machineRouting245').replace('oldStatePrefix246','oldStateRouting245').replace('Fin 246','Fin 245').replace('Config 246','Config 245')
s=rename(s0);a=rename(a0)
doc='''/-!
Concrete marking on the exact routing245 table.

Direct port of the checked RegisterMarkPrefix246 proof. All selected old-label
rows are unchanged in source68 (arrival8286787dd0468d848db345debe304b002d7064a4).
The literal245 table is used for every finite row fact; no global machine
renaming or operational meaning for absent labels is assumed.

The original Mira-Cult, Jeff Ketchersid and Wade framework attribution and
source63's old20 selector restoration are retained. Pure unary encodings
and the state-count-generic return scanner come from RegisterMarkPerm252.
Arbitrary values, terminal words, spare suffixes and left contexts remain
quantified, with exact duration 2 * width pre + 3 and the complete tape.
No bootstrap, whole-program, or consistency theorem is asserted here.
-/'''
s=re.sub(r'/\-![\s\S]*?\-/',lambda _:doc,s,count=1)
strip=lambda t:re.sub(r'/\-![\s\S]*?\-/', '',t,count=1)
assert strip(s)==strip(rename(s0));assert a==rename(a0)
assert a.count('#print axioms ')==10 and a.count('\nexample ')==6
assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s)
sp=B/'RegisterMarkRouting245.lean';ap=B/'Audit.lean';assert not sp.exists()and not ap.exists()
sp.write_text(s);ap.write_text(a)
for label,x,y,p0,p1 in [('source',s0,s,sp0,sp),('audit',a0,a,ap0,ap)]:
 (B/f'{label}-from246.diff').write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=str(p0),tofile=str(p1))))
tp=Q/'results/table-routing245-verification.json';mp=Q/'results/prefix246-mark-verification.json'
assert sha(tp)=='bb53b70f1a775b915d9b335a4ce1378c8350f771aca6aa007c0227989fd87281'
assert sha(mp)=='e8b9aac9ad117eadbf63efbac49d8e35e326d1b270a5796b7abbd9434a1d8328'
t=json.loads(tp.read_text());m=json.loads(mp.read_text());assert t['status']==m['status']=='PASS'
mods=['BusyBeaver.Core','BusyBeaver.ZFC.FiniteZipper','BusyBeaver.ZFC.ZipperRuns','BusyBeaver.ZFC.TablePerm252','BusyBeaver.ZFC.RegisterBoxesPerm252','BusyBeaver.ZFC.RegisterMarkPerm252']
providers=[]
for name in mods:
 x=next(x for x in m['reused_modules']if x['module']==name);source=L/pathlib.Path(name.replace('.','/')).with_suffix('.lean')
 assert sha(source)==x['source_sha256'] and sha(x['object'])==x['object_sha256']
 h=next(y for y in m['actual_first_providers']if y['module']==name)
 assert h['sha256']==x['object_sha256'] and pathlib.Path(h['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
 providers.append(dict(x,source=str(source),selected_parent_record=desc(mp)))
f=next(x for x in t['fresh_modules']if x['module']=='BusyBeaver.ZFC.TableRouting245');table=L/'BusyBeaver/ZFC/TableRouting245.lean'
assert sha(table)==f['source_sha256']and sha(f['path'])==f['sha256']
providers.append(dict(module=f['module'],source=str(table),source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'],selected_parent_record=desc(tp)))
seen=set();external={'Init'}
def visit(name):
 if not name.startswith('BusyBeaver.'):external.add(name);return
 if name in seen:return
 seen.add(name);x=next(x for x in providers if x['module']==name)
 for dep in re.findall(r'^import ([A-Za-z0-9_.]+)$',pathlib.Path(x['source']).read_text(),re.M):visit(dep)
for name in ['BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.RegisterMarkPerm252']:visit(name)
assert seen=={x['module']for x in providers}and len(seen)==7
for x in m['toolchain_providers']:assert sha(x['object'])==x['object_sha256']
boundary=dict(status='SOURCE_ONLY_SEVEN_PROVIDER_BOUNDARY',source=desc(sp),audit=desc(ap),direct_imports=['BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.RegisterMarkPerm252'],project_module_count=7,providers=providers,toolchain_providers=m['toolchain_providers'],external_boundaries=sorted(external),compiler=t['compiler'],selected_parent_records=[desc(tp),desc(mp)],named_probes=10,typed_callers=6,compiler_execution=False,guard_execution=False)
(B/'boundary.json').write_text(json.dumps(boundary,indent=2)+'\n')
# Reuse the just-reviewed245 pulse guard's strengthened parent/provider policy.
gp=pathlib.Path('/tmp/zfc-routing245-lean/pulse/check.py');g0=gp.read_text()
assert sha(gp)=='2e52c0f9f6a5df873c0eeca1e304fe1e4b3098891df05517b8ccf1b98163ce37'
g=g0.replace('Routing245Pulse','RegisterMarkRouting245').replace('exact245 pulse proof; four','exact245 marking proof; seven')
g=g.replace('/tmp/zfc-routing245-lean/pulse/','/tmp/zfc-routing245-lean/mark/')
g=g.replace('57465a4b514feca33a1b1148a3bf51ae92462f97a6f965ad0e1b8dcb53ab2685',sha(sp)).replace('16e971615215c89d9810479d08e5ab8219b7754211eab05b64112d0bed39fdd0',sha(ap))
g=g.replace('PULSE_RECORD_SHA','MARK_RECORD_SHA');g=re.sub(r'\bPULSE\b','MARK',g);g=re.sub(r'\bpulse\b','mark',g)
g=g.replace('prefix246-mark-verification.json','prefix246-mark-verification.json')
g=g.replace('a51632e7a25ba048d8a988a07546637a8937649aec48303d167886f6b16b69e1',sha(mp))
oldguard=pathlib.Path('/tmp/zfc-prefix246-lean/mark/check.py').read_text()
# Extract only literal reviewed declarations; no checker evaluation.
parsed=ast.parse(oldguard);literals={node.targets[0].id:ast.literal_eval(node.value) for node in parsed.body if isinstance(node,ast.Assign)and isinstance(node.targets[0],ast.Name)and node.targets[0].id in ['EXPECTED','PROBES']}
expected='EXPECTED = {\n'+''.join(f'    {k!r}: {v!r},\n'for k,v in literals['EXPECTED'].items())+'}'
g=re.sub(r'EXPECTED = \{[\s\S]*?\n\}',lambda _:expected,g,count=1)
g=re.sub(r'PROBES = \[[^\n]*\]',lambda _:'PROBES = '+repr(literals['PROBES']),g,count=1)
g=g.replace('CALLERS = 4','CALLERS = 6')
g=g.replace("assert imports(S) == ['BusyBeaver.ZFC.TableRouting245', 'BusyBeaver.ZFC.ZipperRuns']","assert imports(S) == ['BusyBeaver.ZFC.TableRouting245', 'BusyBeaver.ZFC.RegisterMarkPerm252']")
g=g.replace("assert re.findall(r'^#print axioms (\\S+)$', A.read_text(), re.M) == [PREFIX + n for n in PROBES]","assert re.findall(r'^#print axioms (\\S+)$', A.read_text(), re.M) == PROBES")
g=g.replace('len(closure) == 4','len(closure) == 7').replace('project_module_count=4','project_module_count=7')
assert g[g.index('deadline = time.monotonic() + TIMEOUT'):]==g0[g0.index('deadline = time.monotonic() + TIMEOUT'):]
assert 'prefix246-mark-verification.json'in g
ast.parse(g)
check=B/'check.py';assert not check.exists();check.write_text(g)
(B/'guard-from-pulse245.diff').write_text(''.join(difflib.unified_diff(g0.splitlines(True),g.splitlines(True),fromfile=str(gp),tofile=str(check))))
inv=dict(status='SOURCE_ONLY_NOT_COMPILED',source=desc(sp),audit=desc(ap),boundary=desc(B/'boundary.json'),guard=desc(check),emitter=desc(pathlib.Path(__file__)),template_source=desc(sp0),template_audit=desc(ap0),guard_template=desc(gp),proof_bodies_exact_after_renaming=True,audit_exact_after_renaming=True,proof_execution_body_unchanged=True,named_probes=10,typed_callers=6,shared_seconds=120,flags=['-j1','-M4096'],default_limits=True,compiler_execution=False,guard_execution=False)
(B/'source-guard-inventory.json').write_text(json.dumps(inv,indent=2)+'\n');print(json.dumps(inv,indent=2))
