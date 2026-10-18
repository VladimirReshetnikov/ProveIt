#!/usr/bin/env python3
"""Bounded exact246 symbolic-executor proof,12 exact prerequisite providers.
Compiles only SymbolicPrefix246 and its audit, serially, using checked Boxes,
Mark and Fast predecessors. Prepare-only performs no compiler/version query.
No dependency rebuild, downloads, or enlarged Lean elaboration options.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.SymbolicPrefix246'
PREFIX='SetTheory.BusyBeaver.ZFC.SymbolicPrefix246.'
SOURCE_SHA='aea11cb4168669f53a11a212ab1834d4725624919b0d4d047b125fc730349aec'
AUDIT_SHA='4db44c5cda6d94c2221a174cc506a3094ec1ca20f9b72548b6c05d5ec1a5d80d'
MP_RECORD_SHA='92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b'
EXPECTED={'BusyBeaver.Core': ('436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6', '2c18d0fc971038cdd3cf5998857f56a88ea1cf33cd11f90f6794866fcc2e1148'), 'BusyBeaver.ZFC.FiniteZipper': ('f7b41631975f0c243bcb6e48a6c566adde0866fb93f7105571e310c18db45066', 'bfbfb31d4cd560b52a65a832777d64f544dc6a1bbbb080829cc1465881d44101'), 'BusyBeaver.ZFC.ZipperRuns': ('fc8f39330f6551fb2b29db22127efbb361dd421290b47ca95d1088d7104a3d48', 'f6280bb230bb5f816c27fcd7789aa16a3890d5a0ac3c0d74bd4ac9a19006e8b6'), 'BusyBeaver.ZFC.TablePerm252': ('d216d7292acf690095048024e2cae2575195ded015acf8e235261b8152e74bd0', '62f26b312a448576ae3b83dbeb336a844fbcf9e1341e67aec79114e553dd67c3'), 'BusyBeaver.ZFC.RegisterBoxesPerm252': ('da0a5c460aba89b9d46dc794fad70a98ac441238ed26c5f7287fa4797a0bd5e7', 'ca74f3f602f975958c6c316071dfc151d1b73d4dcc33c34ce19bc8b07fe76c3e'), 'BusyBeaver.ZFC.RegisterMarkPerm252': ('c646007b54f2d32242f593a60eb770834f3e085a03ee60beb1275aebb796ce41', '6d661f5afac61d31ae82fe20e5c2420216fe2bdb866dbabf5572455061df200c'), 'BusyBeaver.ZFC.WritingRuns': ('9b9c616b66902f3ad88323a750dd8e077dedc514c78b885a2a49a47279214838', '2cc06fe32ca6706ffee51d90849625ee5ecb4a12e5a8fdf9914efe339c9d5b9c')}
PROBES=['box_head', 'box_mark', 'box_increment', 'box_zero_decrement', 'box_positive_decrement', 'box_back', 'skipTarget_sound', 'skipTarget_complete', 'sstep_sound', 'exec_sound', 'matches_sound', 'exec_to_matches', 'exec_to_halt', 'verifies_sound', 'verifiesHalt_sound']
CALLERS=15
TIMEOUT=120
PARENTS={
 'boxes':('bd0671838ff39bbc6d3009c420858747b868988e17fe41b32e8e88ba8db8974a','BusyBeaver.ZFC.Prefix246Boxes'),
 'mark':('e8b9aac9ad117eadbf63efbac49d8e35e326d1b270a5796b7abbd9434a1d8328','BusyBeaver.ZFC.RegisterMarkPrefix246'),
 'fast':('e048c1f6dfca04de875e48344e2c4f2a4fb4d2d0ea7562c87f23f4cd433ba850','BusyBeaver.ZFC.FastTablePrefix246')}
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
for label in PARENTS:p.add_argument('--'+label+'-evidence',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve()
assert not W.is_relative_to(R) and (not W.exists() or not any(W.iterdir()))
S=a.source.resolve() if a.source else R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SymbolicPrefix246.lean'
A=a.audit.resolve() if a.audit else Path(__file__).resolve().parent / 'prefix246_symbolic_audit.lean'
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA
MP=R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json'
assert sha(MP)==MP_RECORD_SHA
mp=json.loads(MP.read_text())
C=Path(mp['compiler']['path']).resolve()
assert sha(C)==mp['compiler']['sha256']
version=mp['compiler']['version'];toolroot=C.parent.parent/'lib/lean'
def imports(path):
 return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(path).read_text(),re.M)
def passed(d):
 assert d['status']=='PASS' and d['only_standard_axioms']
 assert d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit']
 assert len(d['commands'])==2 and [q['label'] for q in d['commands']]==['source','audit']
 assert all(q['exit_code']==0 for q in d['commands'])
 assert d['compiler']['sha256']==sha(C) and d['compiler']['version']==version
passed(mp)
assert imports(S)==['BusyBeaver.ZFC.Prefix246Boxes','BusyBeaver.ZFC.FastTablePrefix246','BusyBeaver.ZFC.RegisterMarkPrefix246','BusyBeaver.ZFC.WritingRuns']
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['SymbolicPrefix246.'+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==CALLERS
for f in (S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',f.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',f.read_text())
selected={};evidence={str(MP):sha(MP)};parent_snapshots=[];parent_summaries=[]
def add_provider(q,e):
 m=q['module'];s=Path(q['source']).resolve();o=Path(q['object']).resolve()
 assert sha(s)==q['source_sha256'] and sha(o)==q['object_sha256']
 row=dict(module=m,source=str(s),source_sha256=sha(s),object=str(o),object_sha256=sha(o),evidence=str(e))
 if m in selected:
  assert (selected[m]['source_sha256'],selected[m]['object_sha256'])==(row['source_sha256'],row['object_sha256'])
 else:selected[m]=row
pool={q['module']:q for q in mp['reused_modules']}
for m,(ss,oo) in EXPECTED.items():
 q=pool[m];s=R/'Computability/BusyBeaver/Lean'/Path(m.replace('.','/')).with_suffix('.lean')
 assert sha(s)==ss==q['source_sha256'] and q['object_sha256']==oo
 add_provider(dict(q,source=str(s)),MP)
for label,(pin,module) in PARENTS.items():
 E=getattr(a,label+'_evidence').resolve();assert sha(E)==pin
 parent=json.loads(E.read_text());passed(parent);evidence[str(E)]=pin
 for q in parent['reused_modules']:add_provider(q,E)
 fresh=[q for q in parent['fresh_modules'] if q['module']==module];assert len(fresh)==1
 q=fresh[0];s=Path(parent['source']['path']).resolve();snap=Path(parent['source']['snapshot']).resolve()
 assert q['source_sha256']==parent['source']['sha256']==sha(s)==sha(snap)
 assert sha(q['path'])==q['sha256']
 add_provider(dict(module=module,source=str(s),source_sha256=sha(s),object=q['path'],object_sha256=q['sha256']),E)
 parent_snapshots.append(snap)
 recorded=parent.get('source_object_recorded_before_audit',False)
 if label in ('boxes','mark'):
  assert recorded and parent['source_pass_object']==q
 parent_summaries.append(dict(label=label,evidence=str(E),module=module,
  source_object_recorded_before_audit=recorded,source_sha256=sha(s),object_sha256=q['sha256']))
 for ref in parent.get('provider_evidence',parent.get('parent_evidence',[])):
  f=Path(ref['path']).resolve();assert sha(f)==ref['sha256']
  passed(json.loads(f.read_text()));evidence[str(f)]=ref['sha256']
visiting, closure, tool_names = set(), [], {'Init'}
def visit(m):
    if m in closure:
        return
    assert m in selected and m not in visiting
    visiting.add(m)
    for n in imports(selected[m]['source']):
        if n == 'Init' or n.startswith(('Lean.', 'Std.')):
            tool_names.add(n)
        else:
            visit(n)
    visiting.remove(m)
    closure.append(m)
for m in imports(S):
    visit(m)
assert set(closure) == set(selected) and len(closure) == 12
W.mkdir(parents=True, exist_ok=True)
cache, snap = W / 'cache', W / 'sources'
cache.mkdir()
ss = snap / Path(MODULE.replace('.', '/')).with_suffix('.lean')
ss.parent.mkdir(parents=True)
aa = snap / 'Audit.lean'
shutil.copyfile(S, ss)
shutil.copyfile(A, aa)
for m in closure:
    dest = cache / Path(m.replace('.', '/')).with_suffix('.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.symlink_to(selected[m]['object'])
def first(m):
    rel = Path(m.replace('.', '/')).with_suffix('.olean')
    return next(q / rel for q in (cache, toolroot) if (q / rel).is_file())
actual = []
for m in closure:
    obj = first(m)
    assert sha(obj) == selected[m]['object_sha256']
    actual.append(dict(module=m, actual_first=str(obj), resolved=str(obj.resolve()), sha256=sha(obj)))
tools = []
for m in sorted(tool_names):
    ref = toolroot / Path(m.replace('.', '/')).with_suffix('.olean')
    obj = first(m)
    assert obj.resolve() == ref.resolve()
    tools.append(dict(module=m, object=str(ref), object_sha256=sha(ref), actual_first=str(obj)))
inputs = [Path(__file__).resolve(), S, A, MP, C, ss, aa] + [Path(f) for f in evidence] + parent_snapshots
for q in selected.values():
    inputs += [Path(q['source']), Path(q['object'])]
inputs += [Path(q['object']) for q in tools]
inputs = list(dict.fromkeys(q.resolve() for q in inputs))
before = {str(q): sha(q) for q in inputs}
env = dict(os.environ, LEAN_PATH=str(cache), LEAN_NUM_THREADS='1')
r = dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING', scope=__doc__,
    prepare_only=a.prepare_only, compiler=dict(path=str(C), version=version, sha256=sha(C),
    compiler_version_query_performed=False), source_overridden=a.source is not None,
    audit_overridden=a.audit is not None, source=dict(path=str(S), sha256=sha(S), snapshot=str(ss)),
    audit=dict(path=str(A), sha256=sha(A), snapshot=str(aa)),
    provider_evidence=[dict(path=f, sha256=h) for f,h in evidence.items()], parent_summaries=parent_summaries,
    reused_modules=[selected[m] for m in closure], exact_project_import_closure=True,
    project_module_count=12, external_project_boundaries=[], toolchain_providers=tools,
    actual_first_providers=actual, actual_direct_tool_imports=sorted(tool_names),
    before=before, commands=[], fresh_modules=[], LEAN_PATH=env['LEAN_PATH'],
    dependency_build=False, downloads=False, per_command_timeout_seconds=TIMEOUT,
    shared_wall_seconds=TIMEOUT)
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
