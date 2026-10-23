"""Owned diagnostic fresh check of changed mathematical import closures.

This never accepts the stopped full-run prefix as a basis and never reuses its
objects. All selected mathematical modules compile fresh. It cannot establish
the machine endpoint; the separate frozen full run remains mandatory.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, signal, time

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
SUP = ROOT / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
SUP_SHA = 'a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
def save(p, data):
    with p.open('x') as stream: json.dump(data, stream, indent=2); stream.write('\n')
def profiles(text):
    return [[name, sorted(set(a.strip() for a in atoms.split(',') if a.strip()))]
            for name, atoms in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)]

parser = argparse.ArgumentParser()
parser.add_argument('--spec', type=Path, required=True)
parser.add_argument('--spec-sha', required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
def interrupt(signum, frame):
    raise KeyboardInterrupt(f'Signal {signum}')
signal.signal(signal.SIGTERM, interrupt)
assert sha(args.spec) == args.spec_sha and sha(SUP) == SUP_SHA and sha(LEAN) == LEAN_SHA
spec = read(args.spec)
out = args.out.absolute(); assert not out.exists(); out.mkdir(parents=True)
rows = spec['modules']; names = {r['module'] for r in rows}; assert len(names) == len(rows)
assert not any('KSites215Batch' in m or 'KSource215FwdCheck' in m for m in names)
for r in rows: assert sha(r['source']) == r['source_sha256']
save(out / 'before.json', {'spec_sha256': args.spec_sha, 'driver_sha256': sha(__file__), 'supervisor_sha256': SUP_SHA, 'lean_sha256': LEAN_SHA, 'modules': rows})
loader = importlib.util.spec_from_file_location('owned_diagnostic_supervisor', SUP)
supervisor = importlib.util.module_from_spec(loader); loader.loader.exec_module(supervisor)
workspace = out / 'workspace'; cache = out / 'objects'; workspace.mkdir(); cache.mkdir()
env = os.environ.copy(); env['LEAN_PATH'] = str(cache); env['LEAN_NUM_THREADS'] = '1'
done = {}; started = time.monotonic()
for index, r in enumerate(rows, 1):
    m = r['module']; source = workspace / (m.replace('.', '/') + '.lean')
    source.parent.mkdir(parents=True, exist_ok=True); source.write_bytes(Path(r['source']).read_bytes())
    assert sha(source) == r['source_sha256']
    attempt = out / 'attempts' / (str(index).zfill(3) + '-' + m); attempt.mkdir(parents=True)
    (attempt / source.name).write_bytes(source.read_bytes())
    obj = cache / (m.replace('.', '/') + '.olean'); obj.parent.mkdir(parents=True, exist_ok=True)
    deps = {d: done[d]['object_sha256'] for d in r['imports'] if d != 'Init'}
    for d, h in deps.items(): assert sha(cache / (d.replace('.', '/') + '.olean')) == h
    command = [str(LEAN), '-j1', '-M12288', '--root=' + str(workspace), '-o', str(obj), str(source)]
    log = attempt / 'compiler.log'; record = attempt / 'record.json'
    rec = {'module': m, 'source': str(source), 'source_sha256': r['source_sha256'], 'dependencies': deps,
           'command': command, 'timeout_seconds': 120, 'memory_mebibytes': 12288,
           'compiler_sha256': LEAN_SHA, 'supervisor_sha256': SUP_SHA, 'log': str(log)}
    print('CHECK', m, flush=True)
    ok = supervisor.run_locked(command, ROOT, env, Path('/tmp/proveit-k215-proof-build.lock'), log, 120, rec, record)
    text = log.read_text(); rec.update(warnings=text.count('warning:'), reports=profiles(text), object_sha256=sha(obj) if ok else None)
    supervisor.save(record, rec)
    print(rec['status'], m, flush=True)
    assert ok and not rec['timed_out'] and rec['warnings'] == 0 and 'sorryAx' not in text and 'error:' not in text, m
    assert rec['reports'] == r['expected_reports'], m
    done[m] = rec
    supervisor.save(out / 'completed.json', done)
for r in rows:
    assert sha(r['source']) == r['source_sha256']
    rec = done[r['module']]
    assert sha(rec['log']) == rec['log_sha256']
    assert sha(cache / (r['module'].replace('.', '/') + '.olean')) == rec['object_sha256']
assert sha(args.spec) == args.spec_sha and sha(SUP) == SUP_SHA and sha(LEAN) == LEAN_SHA
save(out / 'result.json', {'status': 'PASS_FRESH_MATHEMATICAL_DIAGNOSTIC_ONLY', 'modules': len(rows), 'seconds': time.monotonic() - started,
     'spec_sha256': args.spec_sha, 'driver_sha256': sha(__file__), 'warnings': 0,
     'scope': 'Fresh mathematical modules only, no stopped-prefix object reuse. Not an accepted full endpoint basis.'})
print('COMPLETE_DIAGNOSTIC_ONLY', len(rows), flush=True)
