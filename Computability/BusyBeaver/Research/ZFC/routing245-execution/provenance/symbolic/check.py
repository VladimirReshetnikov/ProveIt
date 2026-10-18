#!/usr/bin/env python3
"""Bounded exact245 symbolic-executor proof with12 exact providers.
Reuses the actual Pulse/Boxes/Mark/Fast PASS records and only seven generic
providers from the checked246 symbolic record. Source and audit share120s,
-j1 -M4096, default proof limits. No dependency rebuild, download or version
query. This proves checker soundness; all-site acceptance/startup/PA are separate.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.SymbolicRouting245'
PREFIX='SetTheory.BusyBeaver.ZFC.SymbolicRouting245.'
SOURCE_SHA='1558af317333dc3f3fa860838ebcf5af8b3745a8bf1748446c59b3ab1243550d'
AUDIT_SHA='b23bd95479021b73a54b514ca028207133c45d02f6dc995142ec146b53ce33d2'
LEGACY_SHA='bc645cbef2250dcc8adc989640f995a075e5d6d987393789a15b960cb2ad920e'
BOUNDARY_SHA='f204aaa9fa2c167cb5c1ab078b619bf997fe2df67d4ad36421af7e8f4de819c6'
EXPECTED={'BusyBeaver.Core': ('436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6', '2c18d0fc971038cdd3cf5998857f56a88ea1cf33cd11f90f6794866fcc2e1148'), 'BusyBeaver.ZFC.FiniteZipper': ('f7b41631975f0c243bcb6e48a6c566adde0866fb93f7105571e310c18db45066', 'bfbfb31d4cd560b52a65a832777d64f544dc6a1bbbb080829cc1465881d44101'), 'BusyBeaver.ZFC.ZipperRuns': ('fc8f39330f6551fb2b29db22127efbb361dd421290b47ca95d1088d7104a3d48', 'f6280bb230bb5f816c27fcd7789aa16a3890d5a0ac3c0d74bd4ac9a19006e8b6'), 'BusyBeaver.ZFC.TablePerm252': ('d216d7292acf690095048024e2cae2575195ded015acf8e235261b8152e74bd0', '62f26b312a448576ae3b83dbeb336a844fbcf9e1341e67aec79114e553dd67c3'), 'BusyBeaver.ZFC.RegisterBoxesPerm252': ('da0a5c460aba89b9d46dc794fad70a98ac441238ed26c5f7287fa4797a0bd5e7', 'ca74f3f602f975958c6c316071dfc151d1b73d4dcc33c34ce19bc8b07fe76c3e'), 'BusyBeaver.ZFC.RegisterMarkPerm252': ('c646007b54f2d32242f593a60eb770834f3e085a03ee60beb1275aebb796ce41', '6d661f5afac61d31ae82fe20e5c2420216fe2bdb866dbabf5572455061df200c'), 'BusyBeaver.ZFC.WritingRuns': ('9b9c616b66902f3ad88323a750dd8e077dedc514c78b885a2a49a47279214838', '2cc06fe32ca6706ffee51d90849625ee5ecb4a12e5a8fdf9914efe339c9d5b9c')}
PROBES=['box_head', 'box_mark', 'box_increment', 'box_zero_decrement', 'box_positive_decrement', 'box_back', 'skipTarget_sound', 'skipTarget_complete', 'sstep_sound', 'exec_sound', 'matches_sound', 'exec_to_matches', 'exec_to_halt', 'verifies_sound', 'verifiesHalt_sound']
PARENTS={'pulse': ('/tmp/zfc-routing245-lean/pulse/run1/verification.json', 'c756bf41b8f2f778d0c6c21e8de0e54a3625cc69253607cb7e0f6fe1c3c605fb', 'BusyBeaver.ZFC.Routing245Pulse', 3, 4), 'boxes': ('/tmp/zfc-routing245-lean/boxes/run2/verification.json', '43b9452404e2307d0dcab4ce1d7a03fdf467196aefb5b8c82f529ec5d2c8ca4c', 'BusyBeaver.ZFC.Routing245Boxes', 14, 19), 'mark': ('/tmp/zfc-routing245-lean/mark/run1/verification.json', '01ee8913958cf55cd3774fd3aa3fb76e8b6ddbd1b27daf90cf37618ae0dcf25a', 'BusyBeaver.ZFC.RegisterMarkRouting245', 10, 6), 'fast': ('/tmp/zfc-routing245-lean/fast-table/run1/verification.json', 'b9aa533b7e04c59a382147b3c165c20e2366be008981e43695050e4ac705b09d', 'BusyBeaver.ZFC.FastTableRouting245', 2, 4)}
CALLERS=15
TIMEOUT=120
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
for label,spec in PARENTS.items():p.add_argument('--'+label+'-evidence',type=Path,default=Path(spec[0]))
p.add_argument('--legacy-evidence',type=Path)
p.add_argument('--boundary',type=Path,default=HERE/'resolved-boundary.json')
p.add_argument('--output',type=Path,required=True)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve()
assert not W.is_relative_to(R) and(not W.exists()or not any(W.iterdir()))
S=a.source.resolve()if a.source else HERE/'SymbolicRouting245.lean'
A=a.audit.resolve()if a.audit else HERE/'Audit.lean'
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA
E0=a.legacy_evidence.resolve()if a.legacy_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/prefix246-symbolic-verification.json'
BP=a.boundary.resolve();assert sha(E0)==LEGACY_SHA and sha(BP)==BOUNDARY_SHA
legacy=json.loads(E0.read_text());boundary=json.loads(BP.read_text())
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
passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(15,15)
assert imports(S)==['BusyBeaver.ZFC.Routing245Boxes','BusyBeaver.ZFC.FastTableRouting245','BusyBeaver.ZFC.RegisterMarkRouting245','BusyBeaver.ZFC.WritingRuns']
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['SymbolicRouting245.'+n for n in PROBES]
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
assert boundary['source']['sha256']==SOURCE_SHA and boundary['audit']['sha256']==AUDIT_SHA
assert boundary['project_count']==12 and boundary['named_probes']==15 and boundary['typed_callers']==15
assert len(boundary['providers'])==len(selected)==12
for row in boundary['providers']:
 q=selected[row['module']];assert all(q[k]==row[k]for k in('source','source_sha256','object','object_sha256'))
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
assert set(closure)==set(selected)and len(closure)==12
assert tool_names=={'Init','Lean.Elab.Tactic.Omega'}
assert boundary['toolchain_providers']==legacy['toolchain_providers']
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
inputs=[Path(__file__).resolve(),S,A,E0,BP,C,ss,aa]+[Path(f)for f in evidence]+parent_snapshots
for q in selected.values():inputs+=[Path(q['source']),Path(q['object'])]
inputs+=[Path(q['object'])for q in tools];inputs=list(dict.fromkeys(q.resolve()for q in inputs))
before={str(q):sha(q)for q in inputs}
env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(C.parent.parent))
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,
 prepare_only=a.prepare_only,compiler=dict(path=str(C),version=version,sha256=sha(C),compiler_version_query_performed=False),
 source_overridden=a.source is not None,audit_overridden=a.audit is not None,
 source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),
 provider_evidence=[dict(path=f,sha256=h)for f,h in evidence.items()],parent_summaries=parent_summaries,
 resolved_boundary=dict(path=str(BP),sha256=sha(BP)),reused_modules=[selected[m]for m in closure],exact_project_import_closure=True,
 project_module_count=12,external_project_boundaries=[],toolchain_providers=tools,actual_first_providers=actual,
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
