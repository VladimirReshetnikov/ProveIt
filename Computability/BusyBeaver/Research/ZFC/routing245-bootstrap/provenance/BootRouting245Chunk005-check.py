#!/usr/bin/env python3
"""Bounded exact245 actual blank-run continuation 214016 to 279552.
Exact successful predecessor, generated source/data/table pins and source-object
before audit. Shared120s/-j1/-M4096/default proof limits. No builds/version query.
Runtime framing, coverage and PA comparison remain separate.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.BootRouting245Chunk005'
PREFIX='SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.'
SOURCE_SHA='0f0b1964fe9b5950750a5d1caa1518d56f6918d9bf6cb884958419aee86ecff5'
AUDIT_SHA='6a94de0d810965837d1043074989fd7885cf5f7e99fd6c2a0af4590358d74cf0'
LEGACY_SHA='c756bf41b8f2f778d0c6c21e8de0e54a3625cc69253607cb7e0f6fe1c3c605fb'
EXPECTED={'BusyBeaver.ZFC.FiniteZipper': ('f7b41631975f0c243bcb6e48a6c566adde0866fb93f7105571e310c18db45066', 'bfbfb31d4cd560b52a65a832777d64f544dc6a1bbbb080829cc1465881d44101')}
PROBES=['block230400', 'reached230400', 'block246784', 'reached246784', 'block263168', 'reached263168', 'block279552', 'reached279552']
PARENTS={'previous': ('/tmp/zfc-routing245-lean/bootstrap-chunks/group04/run1/verification.json', 'f137a985a32f6ac09503d13bb6519bc903823eb0cb67dd36f565981596922cbd', 'BusyBeaver.ZFC.BootRouting245Chunk004', 8, 11)}
CALLERS=11
TIMEOUT=120
DATA_SHA='81bf40bd87eed3bc43c06556ef4d8eb18c26f06c8ade3c359dda54c550057678'
INVENTORY_SHA='5f1e5bd1ffcb2197a8ad7d9a96d863b3e1397b787718e0592b4b96e02b277e89'
GENERATOR_SHA='610fa3ae21f146dadf8f2346702b99a54da12cf6271a4427a74e4456bdf03016'
TABLE_SHA='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
for label,spec in PARENTS.items():p.add_argument('--'+label+'-evidence',type=Path,default=Path(spec[0]))
p.add_argument('--legacy-evidence',type=Path)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
assert all(not spec[1].startswith('PENDING_')for spec in PARENTS.values()), 'Freeze the actual successful predecessor record before preparation or proof.'
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve()
assert not W.is_relative_to(R) and(not W.exists()or not any(W.iterdir()))
S=a.source.resolve()if a.source else HERE/'BootRouting245Chunk005.lean'
A=a.audit.resolve()if a.audit else HERE/'Audit.lean'
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA
D=HERE/'data.json';I=HERE/'source-inventory.json';G=Path('/tmp/zfc-routing245-lean/bootstrap-plan/generate.py')
TABLE=R/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245.tm'
assert (sha(D),sha(I),sha(G),sha(TABLE))==(DATA_SHA,INVENTORY_SHA,GENERATOR_SHA,TABLE_SHA)
inventory=json.loads(I.read_text());data=json.loads(D.read_text())
assert inventory['module']==MODULE and inventory['source']['sha256']==SOURCE_SHA and inventory['audit']['sha256']==AUDIT_SHA
assert inventory['data']['sha256']==DATA_SHA and inventory['generator']['sha256']==GENERATOR_SHA and inventory['canonical']['sha256']==TABLE_SHA
assert inventory['unit_index']==5 and inventory['start']==214016 and inventory['endpoint']==279552
assert inventory['segments']==[{'start': 214016, 'end': 230400, 'depth': 14}, {'start': 230400, 'end': 246784, 'depth': 14}, {'start': 246784, 'end': 263168, 'depth': 14}, {'start': 263168, 'end': 279552, 'depth': 14}] and inventory['probes']==[PREFIX+n for n in PROBES] and inventory['callers']==CALLERS
assert data['status']=='UNTRUSTED_GENERATED_INPUTS' and data['proof_execution'] is False
assert data['segments']==inventory['segments'] and data['table']['sha256']==TABLE_SHA
ADAPTOR=Path('/tmp/zfc-routing245-lean/bootstrap-plan/prepare_continuation_guard.py');TEMPLATE=Path('/tmp/zfc-routing245-lean/bootstrap-first/check.py');PI=Path('/tmp/zfc-routing245-lean/bootstrap-chunks/group04/source-inventory.json')
assert sha(ADAPTOR)=='25397147110e8417e823a9027085ce72a6dd7ff3c77d514afb7f10484cabdcf2' and sha(TEMPLATE)=='8f8b3b6c734408b5757d62004cdd93f5cd3b7f87614fca27292b1e93554c3714' and sha(PI)=='9ffb4927937b698c13322d156b4dffacfd38de98f009fb0925a789d413af7151'
previous_inventory=json.loads(PI.read_text())
assert previous_inventory['module']=='BusyBeaver.ZFC.BootRouting245Chunk004' and previous_inventory['endpoint']==214016
assert previous_inventory['source']['sha256']=='cbb587663cc47189e1e3a99daa40c66eb1309fd794ad45773be3106fc692bbbd' and previous_inventory['audit']['sha256']=='dab3e5160693d54c4c91fdf6ca9e32961fdc52146f9578dd71686a45ce50993b'
E0=a.legacy_evidence.resolve()if a.legacy_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/routing245-pulse-verification.json'
assert sha(E0)==LEGACY_SHA
legacy=json.loads(E0.read_text())
C=Path(legacy['compiler']['path']).resolve();assert sha(C)==legacy['compiler']['sha256']
version=legacy['compiler']['version'];toolroot=C.parent.parent/'lib/lean'
def imports(path):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(path).read_text(),re.M)
def passed(d):
 assert d['status']=='PASS'and d['prepare_only']is False and d['only_standard_axioms']
 assert d['all_input_provider_postchecks']and d['all_fresh_objects_unchanged_after_audit']and d['before']==d['after']
 assert d['source_object_recorded_before_audit']
 assert len(d['commands'])==2 and[q['label']for q in d['commands']]==['source','audit']
 assert all(q['exit_code']==0 and not q.get('timed_out',False)for q in d['commands'])
 assert d['compiler']['sha256']==sha(C)and d['compiler']['version']==version and Path(d['compiler']['path']).resolve()==C
passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(3,4)
assert imports(S)==['BusyBeaver.ZFC.BootRouting245Chunk004']
assert 'theorem reached279552 : ZipRep (machineRouting245.run 279552) checkpoint279552' in S.read_text()
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==CALLERS
for f in(S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',f.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',f.read_text())
selected={};evidence={str(E0):sha(E0)};parent_snapshots=[];parent_summaries=[]
def first_path(d):return Path(d['actual_first']if'actual_first'in d else d['path']).resolve()
def add_provider(q,e):
 m=q['module'];s=Path(q['source']).resolve();o=Path(q['object']).resolve()
 assert sha(s)==q['source_sha256']and sha(o)==q['object_sha256']
 row=dict(module=m,source=str(s),source_sha256=sha(s),object=str(o),object_sha256=sha(o),evidence=str(e))
 if m in selected:assert(selected[m]['source_sha256'],selected[m]['object_sha256'])==(row['source_sha256'],row['object_sha256'])
 else:selected[m]=row
pool={q['module']:q for q in legacy['reused_modules']}
for m,(ss,oo)in EXPECTED.items():
 q=pool[m];assert(q['source_sha256'],q['object_sha256'])==(ss,oo)
 for k in('source','object'):assert legacy['before'][q[k]]==legacy['after'][q[k]]==q[k+'_sha256']
 actual=next(x for x in legacy['actual_first_providers']if x['module']==m)
 assert actual['sha256']==oo and first_path(actual)==Path(q['object']).resolve()
 add_provider(q,E0)
for label,(_,pin,module,probes,callers)in PARENTS.items():
 E=getattr(a,label+'_evidence').resolve();assert sha(E)==pin
 parent=json.loads(E.read_text());passed(parent);evidence[str(E)]=pin
 assert(parent['named_axiom_probes'],parent['callers'])==(probes,callers)
 actuals={q['module']:q for q in parent['actual_first_providers']}
 for q in parent['reused_modules']:
  for k in('source','object'):assert parent['before'][q[k]]==parent['after'][q[k]]==q[k+'_sha256']
  actual=actuals[q['module']];assert actual['sha256']==q['object_sha256']and first_path(actual)==Path(q['object']).resolve()
  add_provider(q,E)
 fresh=[q for q in parent['fresh_modules']if q['module']==module];assert len(fresh)==1
 q=fresh[0];saved=parent['source_pass_object']
 assert all(saved[k]==q[k]for k in('module','path','sha256','source_sha256'))
 for role in('source','audit'):
  s=Path(parent[role]['path']).resolve();snap=Path(parent[role]['snapshot']).resolve()
  assert sha(s)==sha(snap)==parent[role]['sha256']==parent['before'][str(s)]==parent['after'][str(s)]
  parent_snapshots.extend([s,snap])
 s=Path(parent['source']['path']).resolve()
 assert q['source_sha256']==parent['source']['sha256']and sha(q['path'])==q['sha256']
 actual=parent['fresh_first_provider_before_audit']
 assert actual['module']==module and actual['sha256']==q['sha256']and first_path(actual)==Path(q['path']).resolve()
 add_provider(dict(module=module,source=str(s),source_sha256=sha(s),object=q['path'],object_sha256=q['sha256']),E)
 parent_summaries.append(dict(label=label,evidence=str(E),module=module,source_object_recorded_before_audit=True,source_sha256=sha(s),object_sha256=q['sha256']))
 for ref in parent.get('provider_evidence',parent.get('parent_evidence',[])):
  f=Path(ref['path']).resolve();assert sha(f)==ref['sha256'];evidence[str(f)]=ref['sha256']
visiting,closure,tool_names=set(),[],{'Init'}
def visit(m):
 if m in closure:return
 assert m in selected and m not in visiting
 visiting.add(m)
 for n in imports(selected[m]['source']):
  if n=='Init'or n.startswith(('Lean.','Std.')):tool_names.add(n)
  else:visit(n)
 visiting.remove(m);closure.append(m)
for m in imports(S):visit(m)
assert set(closure)==set(selected)and len(closure)==9
assert tool_names=={'Init','Lean.Elab.Tactic.Omega'}
tool_pins={q['module']:q['object_sha256']for q in legacy['toolchain_providers']}
W.mkdir(parents=True,exist_ok=True);cache,snap=W/'cache',W/'sources';cache.mkdir()
ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True)
aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for m in closure:
 dest=cache/Path(m.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(selected[m]['object'])
def first(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 return next(q/rel for q in(cache,toolroot)if(q/rel).is_file())
actual=[]
for m in closure:
 obj=first(m);assert sha(obj)==selected[m]['object_sha256']
 actual.append(dict(module=m,actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
tools=[]
for m in sorted(tool_names):
 ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');obj=first(m)
 assert obj.resolve()==ref.resolve()and sha(obj)==tool_pins[m]
 tools.append(dict(module=m,object=str(ref),object_sha256=sha(ref),actual_first=str(obj)))
inputs=[Path(__file__).resolve(),S,A,D,I,G,TABLE,ADAPTOR,TEMPLATE,PI,E0,C,ss,aa]+[Path(f)for f in evidence]+parent_snapshots
for q in selected.values():inputs+=[Path(q['source']),Path(q['object'])]
inputs+=[Path(q['object'])for q in tools];inputs=list(dict.fromkeys(q.resolve()for q in inputs))
before={str(q):sha(q)for q in inputs}
env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(C.parent.parent))
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,
 prepare_only=a.prepare_only,compiler=dict(path=str(C),version=version,sha256=sha(C),compiler_version_query_performed=False),
 source_overridden=a.source is not None,audit_overridden=a.audit is not None,
 source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),
 provider_evidence=[dict(path=f,sha256=h)for f,h in evidence.items()],parent_summaries=parent_summaries,
 generated_inputs=dict(inventory=dict(path=str(I),sha256=sha(I)),data=dict(path=str(D),sha256=sha(D)),generator=dict(path=str(G),sha256=sha(G)),canonical=dict(path=str(TABLE),sha256=sha(TABLE)),adaptor=dict(path=str(ADAPTOR),sha256=sha(ADAPTOR)),template=dict(path=str(TEMPLATE),sha256=sha(TEMPLATE)),previous_inventory=dict(path=str(PI),sha256=sha(PI))),
 reused_modules=[selected[m]for m in closure],exact_project_import_closure=True,
 project_module_count=9,external_project_boundaries=[],toolchain_providers=tools,actual_first_providers=actual,
 actual_direct_tool_imports=sorted(tool_names),before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],
 dependency_build=False,downloads=False,per_command_timeout_seconds=TIMEOUT,shared_wall_seconds=TIMEOUT)
def save():
    (W / 'verification.json').write_text(json.dumps(r, indent=2) + '\n')
def post():
    after = {str(q): sha(q) for q in inputs}
    assert before == after
    for m in closure:
        assert sha(first(m)) == selected[m]['object_sha256']
    for q in tools:
        assert sha(first(q['module'])) == q['object_sha256']
    r.update(after=after, all_input_provider_postchecks=True)
save()
if a.prepare_only:
    post()
    save()
    print(W / 'verification.json')
    raise SystemExit(0)
deadline = time.monotonic() + TIMEOUT
def run(label, source, obj=None):
    cmd = [str(C), '-j1', '-M4096', '--root=' + str(snap)]
    if obj is not None:
        cmd += ['-o', str(obj)]
    cmd += [str(source)]
    began = time.monotonic()
    remaining = deadline - began
    assert remaining > 0, 'Shared proof wall budget exhausted.'
    try:
        cp = subprocess.run(cmd, cwd=snap, env=env, text=True, capture_output=True, timeout=remaining)
        output, code = cp.stdout + cp.stderr, cp.returncode
    except subprocess.TimeoutExpired as ex:
        def decoded(x):
            return x.decode(errors='replace') if isinstance(x, bytes) else x or ''
        output, code = decoded(ex.stdout) + decoded(ex.stderr) + '\nTIMEOUT\n', -1
    (W / (label + '.log')).write_text(output)
    r['commands'].append(dict(label=label, command=cmd, seconds=time.monotonic() - began,
                              exit_code=code, output=output))
    save()
    assert code == 0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output, output
    return output
try:
    obj = cache / Path(MODULE.replace('.', '/')).with_suffix('.olean')
    run('source', ss, obj)
    assert obj.is_file() and not obj.is_symlink()
    oh = sha(obj)
    source_object = dict(module=MODULE, path=str(obj), sha256=oh, source_sha256=sha(S))
    r.update(source_object_recorded_before_audit=True, source_pass_object=source_object,
             fresh_modules=[source_object])
    assert first(MODULE).resolve() == obj.resolve()
    r['fresh_first_provider_before_audit'] = dict(module=MODULE, path=str(first(MODULE)), sha256=sha(first(MODULE)))
    save()
    audit_output = run('audit', aa)
    reports = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", audit_output, re.S)
    assert [n for n, _ in reports] == [PREFIX + n for n in PROBES]
    assert all({x.strip() for x in axioms.split(',') if x.strip()} <=
               {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in reports)
    r['actual_axiom_sets'] = [dict(name=name, axioms=[x.strip() for x in block.split(',') if x.strip()]) for name, block in reports]
    post()
    assert sha(obj) == oh and sha(first(MODULE)) == oh
    r.update(status='PASS', all_fresh_objects_unchanged_after_audit=True,
             named_axiom_probes=len(PROBES), callers=CALLERS, only_standard_axioms=True,
             warnings={q['label']: q['output'].count('warning:') for q in r['commands']})
except Exception as ex:
    r.update(status='FAIL', error=str(ex))
    try:
        post()
    except Exception as post_error:
        r['postcheck_error'] = str(post_error)
    save()
    raise
save()
print(W / 'verification.json')
