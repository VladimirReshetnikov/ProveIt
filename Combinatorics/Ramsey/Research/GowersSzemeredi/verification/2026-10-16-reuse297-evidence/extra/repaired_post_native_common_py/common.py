"""Read-only source and native-artifact checks for one pinned source snapshot."""
from pathlib import Path
import datetime, functools, hashlib, json, os, re, subprocess
CHECKER = 'Combinatorics/Ramsey/scripts/check_gowers.py'
CONFIGS = [CHECKER, 'lean-toolchain', 'lake-manifest.json']
INVENTORY = 'Combinatorics/Ramsey/gowers-proof-status.json'
FACADES = ['Combinatorics/Ramsey/Lean/GowersSzemeredi.lean',
           'Combinatorics/Ramsey/Lean/GowersSzemeredi/Audit.lean',
           'Combinatorics/Ramsey/Lean/GowersSzemeredi/PortImportAudit.lean']
def canonical(value): return json.dumps(value, sort_keys=True, separators=(',', ':'))
def same(a, b): return canonical(a) == canonical(b)
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def require(ok, message):
    if not ok: raise RuntimeError(message)
def write_new(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2); stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    Path(path).chmod(0o444)
def git(root, *args, data=None):
    return subprocess.check_output(['git', '--no-optional-locks', *args], cwd=root, input=data)
def head(root): return git(root, 'rev-parse', 'HEAD').decode().strip()
def stamp(path):
    s = Path(path).stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]
def module_path(module):
    require(bool(re.fullmatch(r'(GowersSzemeredi|OAI)(?:\.[A-Za-z0-9_]+)*', module)), 'Invalid local module')
    base = 'Combinatorics/Ramsey/Lean/' if module.split('.')[0] == 'GowersSzemeredi' else 'lib/openai-math/lean/'
    return base + module.replace('.', '/') + '.lean'
def local(module): return module.split('.')[0] in ('GowersSzemeredi', 'OAI')
def graph_for(root, roots):
    graph = {}; active = set()
    def visit(module):
        require(module not in active, 'Cyclic local imports: ' + module)
        if module in graph: return
        active.add(module)
        deps = re.findall(r'^import\s+(\S+)', (root / module_path(module)).read_text(), re.M)
        for dep in deps:
            if local(dep): visit(dep)
        graph[module] = deps; active.remove(module)
    for module in roots: visit(module)
    return dict(sorted(graph.items()))
def describe_modes(root, modes, graph):
    @functools.lru_cache(None)
    def closure(module):
        return frozenset({module}).union(*(closure(d) for d in graph[module] if local(d)))
    result = {}; cumulative = set()
    for label, spec in modes.items():
        roots = spec['roots']; require(len(roots) == len(set(roots)) and roots, 'Duplicate/empty roots')
        modules = sorted(set().union(*(closure(m) for m in roots))); cumulative.update(modules)
        result[label] = {'roots': roots, 'modules': modules, 'module_count': len(modules),
                         'input_count': len(modules) + len(CONFIGS),
                         'source_lines': sum(len((root / module_path(m)).read_text().splitlines()) for m in modules),
                         'cumulative_modules': sorted(cumulative)}
    return result

def committed(root, commit, mapping):
    require(bool(re.fullmatch('[0-9a-f]{40}', commit)), 'Invalid commit')
    for p in mapping:
        require(not Path(p).is_absolute() and '..' not in Path(p).parts and '\n' not in p and ':' not in p, 'Unsafe Git path')
    data = ''.join(commit + ':' + p + '\n' for p in mapping).encode()
    raw = git(root, 'cat-file', '--batch', data=data); offset = 0
    for path, expected in mapping.items():
        end = raw.index(b'\n', offset); parts = raw[offset:end].split()
        require(len(parts) == 3 and parts[1] == b'blob', 'Missing committed source: ' + path)
        size = int(parts[2]); actual = hashlib.sha256(raw[end + 1:end + 1 + size]).hexdigest()
        require(actual == expected, 'Committed source mismatch: ' + path); offset = end + size + 2
    require(offset == len(raw), 'Unexpected Git output')

def source_guard(snapshot):
    root = Path(snapshot['root']); modes = snapshot['modes']; expected = snapshot['source_hashes']
    require(head(root) == snapshot['source_commit'] and git(root, 'status', '--porcelain') == b'', 'HEAD changed or working tree dirty')
    require(list(modes) == ['core', 'shared', 'supplemental'], 'Unexpected mode order')
    graph = graph_for(root, [r for spec in modes.values() for r in spec['roots']])
    require(same(graph, snapshot['graph']), 'Import graph changed')
    require(same(describe_modes(root, modes, graph), modes), 'Closure/count metadata mismatch')
    paths = {module_path(m) for m in graph} | set(CONFIGS + FACADES + [INVENTORY])
    require(set(expected) == paths, 'Protected source keyset mismatch')
    actual = {p: sha(root / p) for p in sorted(paths)}
    require(same(actual, expected), 'Source/config/checker/inventory/facade hash mismatch')
    committed(root, snapshot['source_commit'], actual)
    return {'source_commit': head(root), 'protected_file_count': len(actual), 'source_hashes': actual}

def worker_check(root, allowed_checker=None):
    others = []; lean = []
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid(): continue
        try:
            args = [x.decode() for x in (proc / 'cmdline').read_bytes().split(b'\0') if x]
            if not args: continue
            bases = [Path(x).name for x in args]
            runner = any(re.fullmatch(r'gowers_run_.*_audits(?:_repair[0-9]+|_repaired)?\.py', b) for b in bases)
            runner = runner or any(Path(arg).name == 'run.py' and 'gowers' in arg and 'native' in arg for arg in args)
            if bases[0] != 'lean' and 'check_gowers.py' not in bases and not runner: continue
            cwd = (proc / 'cwd').resolve(strict=True)
            if not cwd.is_relative_to(root) and not any(str(root) in x for x in args): continue
            pid = int(proc.name)
            if pid == allowed_checker:
                require('check_gowers.py' in bases, 'Unexpected checker process'); continue
            parent = int(re.search(r'^PPid:\s+(\d+)', (proc / 'status').read_text(), re.M)[1])
            if allowed_checker is not None and bases[0] == 'lean' and parent == allowed_checker: lean.append(pid)
            else: others.append(pid)
        except (FileNotFoundError, ProcessLookupError): continue
    require(not others and len(lean) <= 1, f'Overlapping native workers: {others}, {lean}')

def artifacts(snapshot, modules, fresh):
    root = Path(snapshot['root']); output = root / '.lake/build/lib/lean'; result = {}
    for module in modules:
        path = output / (module.replace('.', '/') + '.olean')
        if not path.exists():
            require(not fresh, 'Missing artifact: ' + module); result[module] = None; continue
        s = path.stat()
        deps = [output / (d.replace('.', '/') + '.olean') for d in snapshot['graph'][module] if local(d)]
        inputs = [root / module_path(module), *(root / p for p in CONFIGS), *deps]
        current = all(p.exists() and p.stat().st_mtime < s.st_mtime for p in inputs)
        require(current or not fresh, 'Stale artifact: ' + module)
        result[module] = {'mtime_ns': s.st_mtime_ns, 'size': s.st_size, 'fresh': current}
    for module, value in result.items():
        path = output / (module.replace('.', '/') + '.olean')
        require((not path.exists()) if value is None else
                [path.stat().st_mtime_ns, path.stat().st_size] == [value['mtime_ns'], value['size']],
                'Artifact changed during measurement: ' + module)
    return result

def terminal_fields(command, started_at, finished_at, exit_code, log, count):
    text = log.read_text(); matches = re.findall(r'^Checked (\d+) modules \(including up-to-date dependencies\)\.$', text, re.M)
    footer = f'Checked {count} modules (including up-to-date dependencies).'
    return {'command': command, 'started_at': started_at, 'finished_at': finished_at, 'terminal_exit': exit_code,
            'terminal_module_count': int(matches[0]) if len(matches) == 1 else None,
            'terminal_module_count_matches': matches == [str(count)] and text.rstrip().endswith(footer),
            'contains_error_diagnostic': bool(re.search(r'error(?:\([^)]*\))?:', text, re.I)),
            'log': str(log), 'log_sha256': sha(log)}
