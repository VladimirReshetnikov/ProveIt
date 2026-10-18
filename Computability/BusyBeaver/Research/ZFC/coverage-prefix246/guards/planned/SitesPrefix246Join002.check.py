#!/usr/bin/env python3
"""Bounded exact246 coverage unit SitesPrefix246Join002; 45 exact project prerequisites.
Fresh source/audit only, default proof limits, -j1 -M4096, shared120seconds.
Both-child coverage composition; no compiler/version/dependency action in prepare-only.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.SitesPrefix246Join002'
PREFIX='SetTheory.BusyBeaver.ZFC.SitesPrefix246.'
SOURCE_SHA='19ffcee9f423488a9c7bcf210e3d20dc158fbf4400e8bf82d18f0b3b364cb2d5'
AUDIT_SHA='894ac243414f96d4f1635390cc53a7af89184b97ba2e52c3a50b278983ce9857'
MP_RECORD_SHA='92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b'
EXPECTED={'BusyBeaver.ZFC.ActualTree254': ('7f4a3782f4ce061478a233d15272c15f2b2aedab688f728f7e7511f186216e71', 'eb70269d619331e91299e835aaacc486fe677a20a5b271e3054015c4a27c6a1a'), 'BusyBeaver.ZFC.Prog254': ('6e564bd1ba179b2d39fccc3b8c86a681ec0dd6529df9cfa2522500eef140cfde', '3c1e41215bbe83bc2669fa72e890e1f363beed274b8baffecf1c6a3f65d20175'), 'BusyBeaver.ZFC.SiteCoverage': ('643aa151328a65ba292214df01a933adc46408a468faabf273bf736457393cf4', '8684c844151075479126abdd9515aa9515586e3d27a14f80d5182b5c9bc7fe91'), 'BusyBeaver.ZFC.RMBisim': ('68c28a182eed06c0f8d266f0d79d8f884f086228a4794da00da51cf02dbbb13b', 'ce485e7770d168e4f0d4adcb4708d9dce539aa42a87917f385259d897a510393'), 'BusyBeaver.ZFC.RMEquiv': ('cc696ec1d000e9201506f652987d94ba17661114ba785b8dcb09b4f958a32a57', '85816422a56c65d1ebb9787ba9dc099b2618706781e43f86d65c9fda4fc06905'), 'BusyBeaver.ZFC.RMDag': ('1acc3a55d22db81eb03748a7b58d2492d449999516bddae75cd39d886d7099c7', '2d61ba6510d4e61c15b72291cb0dd09ace1d6d720e20967202242e237fc8a2f4')}
PROBES=['join_32', 'join_33', 'join_34', 'join_35', 'join_36', 'join_37', 'join_38', 'join_39', 'join_40', 'join_41', 'join_42', 'join_43', 'join_44', 'join_45', 'join_46', 'join_47']
CALLERS=16
TIMEOUT=120
PARENTS={'site':('ed4586b081e531b08e17827f04e0ad31730a8a73c19426cf5d927e207f4714cd','BusyBeaver.ZFC.SitePrefix246')}
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
for label in PARENTS:p.add_argument('--'+label+'-evidence',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--dependencies',type=Path)
p.add_argument('--prepare-only',action='store_true')
DEPENDENCY_PINS={'BusyBeaver.ZFC.SitesPrefix246Join001': {'source_sha256': 'd2dfb57f51b09887f5da49bebeaa67a025ae920381b1d79e08e56cc9e6ea6ebd', 'audit_sha256': 'a051d43286f8ed71c1711d077c1f35126a1a0380fd72cc63438c5486e8e5df24'}, 'BusyBeaver.ZFC.SitesPrefix246Batch016': {'source_sha256': 'a8df35f518a4ca228f23eda58168ccff2ada1dd26fa5506003602393b37aa938', 'audit_sha256': '9f35a8b47e9364ba1bb67812e4913814180b46e1973d6634926c13351dc2961c'}, 'BusyBeaver.ZFC.SitesPrefix246Batch015': {'source_sha256': '29474feafe8524461ac07bd85165b73bdf3eb2f1492771166a4de7927d1efe2e', 'audit_sha256': '0c35ff06a0f7c9b2bc76e3a2fae9f45e33b5763316b163b46c231d766be2249e'}, 'BusyBeaver.ZFC.SitesPrefix246Batch017': {'source_sha256': '9ff3705fb86ecc16c7174f3443b00d84ed0af488c9794c27547d5d1da2f41f89', 'audit_sha256': 'e7027f2a7142216c85ecd03ac36aaceeb04b916c78bcdd474644c7572697ef9c'}, 'BusyBeaver.ZFC.SitesPrefix246Batch018': {'source_sha256': '2cb9cfdc02fb53d5a3e5fe51ce69e30b5f699afdb69d00f6b27c685e775fcbbd', 'audit_sha256': 'f2eb579acd679dcef5ec7d4d290eb0876ae1f6d554a682594dab0b140f339cea'}, 'BusyBeaver.ZFC.SitesPrefix246Batch019': {'source_sha256': '0202e3a8e2fb77ba2581e65d8b5d7c59a360422b721a5b1d883642e40c4bb18c', 'audit_sha256': 'f46b687aa58dfddc686fd75cc1d317c82cb9e446548116cd7a3ea147ae60f572'}, 'BusyBeaver.ZFC.SitesPrefix246Batch020': {'source_sha256': 'aecdf4fbf909aea72d1ef8cc1d458a1f05fc52f966fd4a224cfccf0ef2a8f010', 'audit_sha256': 'f50f3074360e4ae3c3624a433a2080790396f50093176bc5d5cbab65d017db8a'}}
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve()
assert not W.is_relative_to(R) and (not W.exists() or not any(W.iterdir()))
S=a.source.resolve() if a.source else Path('/tmp/zfc-prefix246-lean/coverage/plan-four/SitesPrefix246Join002.lean')
A=a.audit.resolve() if a.audit else Path('/tmp/zfc-prefix246-lean/coverage/plan-four/SitesPrefix246Join002.audit.lean')
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
assert imports(S)==['BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.SiteCoverage', 'BusyBeaver.ZFC.SitePrefix246', 'BusyBeaver.ZFC.SitesPrefix246Join001', 'BusyBeaver.ZFC.SitesPrefix246Batch016', 'BusyBeaver.ZFC.SitesPrefix246Batch015', 'BusyBeaver.ZFC.SitesPrefix246Batch017', 'BusyBeaver.ZFC.SitesPrefix246Batch018', 'BusyBeaver.ZFC.SitesPrefix246Batch019', 'BusyBeaver.ZFC.SitesPrefix246Batch020']
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
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
 assert recorded and parent['source_pass_object']==q
 parent_summaries.append(dict(label=label,evidence=str(E),module=module,
  source_object_recorded_before_audit=recorded,source_sha256=sha(s),object_sha256=q['sha256']))
 for ref in parent.get('provider_evidence',parent.get('parent_evidence',[])):
  f=Path(ref['path']).resolve();assert sha(f)==ref['sha256']
  passed(json.loads(f.read_text()));evidence[str(f)]=ref['sha256']
# Every generated direct predecessor must carry its own exact successful source/audit record.
if DEPENDENCY_PINS:
 assert a.dependencies is not None
 D=a.dependencies.resolve();deprefs=json.loads(D.read_text());assert set(deprefs)==set(DEPENDENCY_PINS)
 evidence[str(D)]=sha(D)
else:
 assert a.dependencies is None or json.loads(a.dependencies.read_text())=={}
 deprefs={}
for module,ref in deprefs.items():
 E=Path(ref['path']).resolve();assert sha(E)==ref['sha256'];parent=json.loads(E.read_text());passed(parent);evidence[str(E)]=sha(E)
 expected=DEPENDENCY_PINS[module]
 assert parent['source']['sha256']==expected['source_sha256'] and parent['audit']['sha256']==expected['audit_sha256']
 assert sha(parent['source']['path'])==sha(parent['source']['snapshot'])==expected['source_sha256']
 assert sha(parent['audit']['path'])==sha(parent['audit']['snapshot'])==expected['audit_sha256']
 assert parent['source_object_recorded_before_audit'] and len(parent['fresh_modules'])==1
 fresh=parent['fresh_modules'][0];assert fresh['module']==module and fresh['source_sha256']==expected['source_sha256']
 assert parent['source_pass_object']==fresh and sha(fresh['path'])==fresh['sha256']
 for q in parent['reused_modules']:add_provider(q,E)
 add_provider(dict(module=module,source=parent['source']['path'],source_sha256=expected['source_sha256'],object=fresh['path'],object_sha256=fresh['sha256']),E)
 parent_snapshots.extend([Path(parent['source']['snapshot']),Path(parent['audit']['snapshot']),Path(parent['audit']['path'])])
 parent_summaries.append(dict(label='generated_direct_dependency',module=module,evidence=str(E),source_sha256=expected['source_sha256'],object_sha256=fresh['sha256'],source_object_recorded_before_audit=True))
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
assert set(closure) == set(selected) and len(closure) == 45
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
    project_module_count=45, external_project_boundaries=[], toolchain_providers=tools,
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
