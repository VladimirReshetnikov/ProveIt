"""Emit a source-only local pulse port from exact checked246 template bytes."""
import difflib,hashlib,json,pathlib,re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs')
B=pathlib.Path('/tmp/zfc-routing245-lean/pulse')
L=R/'Computability/BusyBeaver/Lean';Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
src=L/'BusyBeaver/ZFC/Prefix246Pulse.lean';audit=Q/'prefix246_pulse_audit.lean'
assert sha(src)=='8bf5e5d5d89909c7be458d6cf349d145941365eaae2f5cfd36bbb743988edcbd'
old=src.read_text();olda=audit.read_text()
def rename(t):
 return t.replace('Prefix246Pulse','Routing245Pulse').replace('TablePrefix246','TableRouting245').replace('machinePrefix246','machineRouting245').replace('oldStatePrefix246','oldStateRouting245').replace('rowPrefix246','rowRouting245').replace('Config 246','Config 245')
s=rename(old);a=rename(olda)
doc='''/-!
The two contextual pulse identities for the exact routing245 table.

Direct port of the checked Prefix246Pulse local identities. The four used
old-label actions are unchanged in the routing245 candidate (source68,
arrival 8286787dd0468d848db345debe304b002d7064a4). Only their compact labels
and the binary state type are interpreted through the new literal table.
The zero/zero pulse returns to old255 and reads its deposited one. Both
three-step equations retain arbitrary contexts and every tape cell.

No global invariant, whole-table renaming or startup transport is asserted.
Mira-Cult, Jeff Ketchersid and Wade's original machine/framework attribution
and source63's contextual-fold contribution are retained.
-/'''
s=re.sub(r'/\-![\s\S]*?\-/',lambda _:doc,s,count=1)
# Exact proof-body identity after state/module renaming, apart from documentation.
strip=lambda t:re.sub(r'/\-![\s\S]*?\-/', '', t,count=1)
assert strip(s)==strip(rename(old))
assert a.count('#print axioms ')==3 and a.count('\nexample ')==4
assert not re.search(r'\bsorry\b|\baxiom\s|native_decide|maxHeartbeats|maxRecDepth',s)
sp=B/'Routing245Pulse.lean';ap=B/'Audit.lean'
assert not sp.exists() and not ap.exists();sp.write_text(s);ap.write_text(a)
(B/'source-from246.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile=str(src),tofile=str(sp))))
(B/'audit-from246.diff').write_text(''.join(difflib.unified_diff(olda.splitlines(True),a.splitlines(True),fromfile=str(audit),tofile=str(ap))))
tp=Q/'results/table-routing245-verification.json';pp=Q/'results/prefix246-pulse-verification.json'
t=json.loads(tp.read_text());p=json.loads(pp.read_text());assert t['status']==p['status']=='PASS'
assert sha(tp)=='bb53b70f1a775b915d9b335a4ce1378c8350f771aca6aa007c0227989fd87281'
assert sha(pp)=='a51632e7a25ba048d8a988a07546637a8937649aec48303d167886f6b16b69e1'
providers=[]
for m in ['BusyBeaver.Core','BusyBeaver.ZFC.FiniteZipper','BusyBeaver.ZFC.ZipperRuns']:
 x=next(x for x in p['reused_modules']if x['module']==m)
 assert sha(x['source'])==x['source_sha256'] and sha(x['object'])==x['object_sha256']
 actual=next(y for y in p['actual_first_providers']if y['module']==m)
 assert actual['sha256']==x['object_sha256'] and pathlib.Path(actual['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
 providers.append(dict(x,selected_parent_record=desc(pp)))
f=next(x for x in t['fresh_modules']if x['module']=='BusyBeaver.ZFC.TableRouting245');table=L/'BusyBeaver/ZFC/TableRouting245.lean'
assert sha(table)==f['source_sha256'] and sha(f['path'])==f['sha256']
providers.append(dict(module=f['module'],source=str(table),source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'],selected_parent_record=desc(tp)))
mods={x['module'] for x in providers};seen=set();external={'Init'}
def visit(m):
 if not m.startswith('BusyBeaver.'):external.add(m);return
 if m in seen:return
 seen.add(m);x=next(x for x in providers if x['module']==m)
 for line in pathlib.Path(x['source']).read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
for m in ['BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.ZipperRuns']:visit(m)
assert seen==mods and len(mods)==4
boundary=dict(status='SOURCE_ONLY_FOUR_PROVIDER_BOUNDARY',source=desc(sp),audit=desc(ap),direct_imports=['BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.ZipperRuns'],project_module_count=4,providers=providers,external_boundaries=sorted(external),toolchain_providers=p['toolchain_providers'],compiler=t['compiler'],selected_parent_records=[desc(tp),desc(pp)],named_probes=3,typed_callers=4,compiler_executed=False,guard_executed=False,required_policy=dict(shared_source_audit_seconds=120,compiler_flags=['-j1','-M4096'],proof_limits='default',no_builds=True,no_version_query=True,fresh_object_before_audit=True))
for x in p['toolchain_providers']:assert sha(x['object'])==x['object_sha256']
(B/'boundary.json').write_text(json.dumps(boundary,indent=2)+'\n')
inv=dict(status='SOURCE_ONLY_NOT_COMPILED',module='BusyBeaver.ZFC.Routing245Pulse',source=desc(sp),audit=desc(ap),emitter=desc(pathlib.Path(__file__)),template_source=desc(src),template_audit=desc(audit),source_delta=desc(B/'source-from246.diff'),audit_delta=desc(B/'audit-from246.diff'),boundary=desc(B/'boundary.json'),proof_bodies_exact_after_renaming=True,named_probes=3,typed_callers=4,source_execution=False,compiler_execution=False,guard_execution=False)
(B/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
print(json.dumps(inv,indent=2))
