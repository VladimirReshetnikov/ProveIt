"""Direct merged-source guard. No historical outcome reuse or native launch."""
from pathlib import Path
import argparse, datetime, functools, hashlib, json, os, re, subprocess, sys
sys.dont_write_bytecode = True
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled')
ROOT = Path('/home/codex/.codex/worktrees/9c9b/Proofs')
BASE = Path('/tmp/gowers-merged-native-tools')
SNAPSHOT = BASE / 'snapshot.json'
SNAPSHOT_SHA = 'ea073d3d780e82c569997118c70dbf880cee2d437ddd8e05e10119e4c602256a'
CHECKER = 'Combinatorics/Ramsey/scripts/check_gowers.py'
INVENTORY = 'Combinatorics/Ramsey/gowers-proof-status.json'
OUTPUT = ROOT / '.lake/build/lib/lean'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
digest = lambda b: hashlib.sha256(b).hexdigest()
def stamp(path):
    s = Path(path).stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]
def when(value):
    t = datetime.datetime.fromisoformat(value)
    assert t.tzinfo is not None
    return t
def error_diagnostic(text):
    return bool(re.search(r'error(?:\([^)]*\))?:', text, re.I))
def module_path(module):
    top = module.split('.')[0]
    assert top in ('GowersSzemeredi', 'OAI')
    prefix = 'Combinatorics/Ramsey/Lean/' if top == 'GowersSzemeredi' else 'lib/openai-math/lean/'
    return prefix + module.replace('.', '/') + '.lean'
def freeze_check(snapshot):
    for p, s in snapshot.items():
        assert stamp(p) == s, ('Protected file changed during invocation', p)
def worker_check(allowed_checker=None):
    """Reject a second workspace runner/checker; allow at most one child Lean worker."""
    found = []; lean = []
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid():
            continue
        try:
            args = [x.decode() for x in (proc / 'cmdline').read_bytes().split(b'\0') if x]
            if not args:
                continue
            bases = [Path(x).name for x in args]
            candidate = bases[0] == 'lean' or any(x == 'check_gowers.py' or re.fullmatch(r'gowers_run_.*_audits(?:_repair[0-9]+|_repaired)?\.py', x) for x in bases)
            if not candidate:
                continue
            cwd = (proc / 'cwd').resolve(strict=True)
            if not cwd.is_relative_to(ROOT) and not any(str(ROOT) in x for x in args):
                continue
            pid = int(proc.name)
            if allowed_checker is not None and pid == allowed_checker:
                assert 'check_gowers.py' in bases
                continue
            if allowed_checker is not None and bases[0] == 'lean':
                status = (proc / 'status').read_text()
                parent = int(re.search(r'^PPid:\s+(\d+)', status, re.M).group(1))
                if parent == allowed_checker:
                    lean.append(pid)
                    continue
            found.append({'pid': pid, 'cwd': str(cwd), 'argv': args})
        except (FileNotFoundError, ProcessLookupError):
            continue
    assert not found and len(lean) <= 1, ('Overlapping workspace native worker', found, lean)
    return {'workspace': str(ROOT), 'other_native_workers': 0, 'maximum_allowed_lean_children': 1}
def artifact_snapshot(ownmaps, graph, require_fresh=True):
    """Existing checker freshness contract, plus mtime_ns/size stability; no content hash claim."""
    modules = sorted(set().union(*(set(x) for x in ownmaps)))
    modules = [m for m in modules if m not in (CHECKER, 'lean-toolchain', 'lake-manifest.json')]
    result = {}
    for module in modules:
        artifact = OUTPUT / (module.replace('.', '/') + '.olean')
        if not artifact.exists():
            assert not require_fresh, ('Missing native artifact', module)
            result[module] = None
            continue
        s = artifact.stat()
        dependencies = [OUTPUT / (d.replace('.', '/') + '.olean') for d in graph[module] if d.split('.')[0] in ('GowersSzemeredi', 'OAI')]
        inputs = [ROOT / module_path(module), ROOT / CHECKER, ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json', *dependencies]
        fresh = all(p.exists() and p.stat().st_mtime < s.st_mtime for p in inputs)
        assert fresh or not require_fresh, ('Stale native artifact', module)
        result[module] = {'mtime_ns': s.st_mtime_ns, 'size': s.st_size, 'fresh': fresh}
    for module, value in result.items():
        artifact = OUTPUT / (module.replace('.', '/') + '.olean')
        if value is None:
            assert not artifact.exists()
        else:
            s = artifact.stat()
            assert [s.st_mtime_ns, s.st_size] == [value['mtime_ns'], value['size']], ('Artifact changed during snapshot', module)
    return result
def git(args, **kw):
    return subprocess.check_output(['git', '--no-optional-locks', *args], cwd=ROOT, **kw)
def head(): return git(['rev-parse', 'HEAD']).decode().strip()
def ancestor(a, b):
    assert re.fullmatch('[0-9a-f]{40}', a or '') and re.fullmatch('[0-9a-f]{40}', b or '')
    assert subprocess.run(['git', '--no-optional-locks', 'merge-base', '--is-ancestor', a, b], cwd=ROOT).returncode == 0

def committed(commit, mapping):
    assert re.fullmatch('[0-9a-f]{40}', commit or '')
    assert all(not Path(p).is_absolute() and '\n' not in p and ':' not in p and '..' not in Path(p).parts for p in mapping)
    raw = git(['cat-file', '--batch'], input=''.join(commit + ':' + p + '\n' for p in mapping).encode()); off = 0
    for p, h in mapping.items():
        end = raw.index(b'\n', off); parts = raw[off:end].split(); assert len(parts) == 3 and parts[1] == b'blob'
        size = int(parts[2]); assert digest(raw[end + 1:end + 1 + size]) == h, (commit, p); off = end + size + 2
    assert off == len(raw)

def guard(source_commit, mode):
    assert mode in ('core', 'shared') and sha(SNAPSHOT) == SNAPSHOT_SHA
    snap = json.loads(SNAPSHOT.read_text()); current = snap['protected_source_hashes']; assert source_commit == snap['source_commit']
    assert str(ROOT) == snap['root'] and head() == source_commit and git(['status', '--porcelain']) == b''
    ancestor(snap['repaired_source_commit'], source_commit); ancestor(snap['incoming_main_commit'], source_commit)
    committed(source_commit, current)
    for p, h in current.items(): assert sha(ROOT / p) == h, p
    graph = {}; cache = {}
    for m, expected in snap['graph'].items():
        text = (ROOT / module_path(m)).read_text(); cache[m] = text
        graph[m] = re.findall(r'^import\s+(\S+)', text, re.M); assert graph[m] == expected
    @functools.lru_cache(None)
    def closure(m):
        return frozenset({m}).union(*(closure(d) for d in graph[m] if d.split('.')[0] in ('GowersSzemeredi', 'OAI')))
    for label, config in snap['modes'].items():
        modules = set().union(*(closure(m) for m in config['roots']))
        assert sorted(modules) == config['modules'] and len(modules) == config['module_count']
        assert len(modules) + len(snap['configs']) == config['input_count']
        assert sum(len(cache[m].splitlines()) for m in modules) == config['source_lines']
    assert set(snap['selected_source_hashes']) == {module_path(m) for m in graph} | set(snap['configs'])
    assert current == {**snap['selected_source_hashes'], **{p: current[p] for p in snap['facades'] + [snap['inventory']]}}
    history = snap['historical_roots_source']; assert sha(history['path']) == history['sha256']
    historical = json.loads(Path(history['path']).read_text())
    assert snap['modes']['shared']['roots'] == [r['target'] for r in historical]
    assert len(snap['own_rows']) == 57 and snap['retained_historical_outcomes'] == 0
    for row, target in zip(snap['own_rows'], snap['modes']['shared']['roots']):
        assert row['target'] == target and len(closure(target)) == row['modules'] and row['inputs'] == row['modules'] + len(snap['configs'])
        assert sum(len(cache[m].splitlines()) for m in closure(target)) == row['source_lines']
    for scope in snap['named_scopes']:
        assert scope['provider'] in closure(scope['target']); text = cache[scope['provider']]
        pattern = r'let checked : Array Name := #\[(.*?)\]' if scope['provider'].endswith('.PrintedExtractionCoreAudit') else r'for name in #\[(.*?)\]\s*do'
        arrays = re.findall(pattern, text, re.S); assert len(arrays) == 1; array = arrays[0]
        if 'definitionName' in array:
            definitions = re.findall(r'let definitionName := ``(\S+)', text); assert len(definitions) == 1
            array = array.replace('definitionName', '``' + definitions[0])
        assert re.findall(r'``([A-Za-z0-9_.]+)', array) == scope['names'] and len(scope['names']) == scope['count']
        allowed = re.findall(r'let allowed : Array Name := #\[(.*?)\]', text, re.S); assert len(allowed) == 1
        assert re.findall(r'``([A-Za-z0-9_.]+)', allowed[0]) == scope['approved_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
    failed_ref = snap['failed_original_core']; assert sha(failed_ref['path']) == failed_ref['sha256']
    failed = json.loads(Path(failed_ref['path']).read_text())
    assert failed['status'] == 'failed' and type(failed['terminal_exit']) is int and failed['terminal_exit'] == 1
    assert failed['source_commit'] == snap['original_source_commit'] and failed['native_source_repairs'] == 0 and snap['native_source_repairs'] == 1
    assert snap['native_result_claimed'] is False
    evidence = {str(SNAPSHOT): SNAPSHOT_SHA, history['path']: history['sha256'], failed_ref['path']: failed_ref['sha256']}
    for p, h in evidence.items(): assert sha(p) == h
    for p, h in current.items(): assert sha(ROOT / p) == h
    return {'snapshot_sha256': SNAPSHOT_SHA, 'source_commit': source_commit, 'mode': mode, 'source_freeze': {str(ROOT / p): stamp(ROOT / p) for p in current}, 'evidence_freeze': {p: stamp(p) for p in evidence}, 'protected_paths': len(current), 'native_source_repairs': 1}
