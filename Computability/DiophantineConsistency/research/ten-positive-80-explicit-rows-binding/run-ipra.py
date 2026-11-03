#!/usr/bin/env python3
"""Check the explicit-row iPRA endpoints on the recorded rebuilt provider."""
from hashlib import sha256
from pathlib import Path
import json, os, re, shutil, subprocess, sys, tempfile, time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
attempt = os.environ.get('ATTEMPT', 'attempt01')
if not re.fullmatch(r'attempt[0-9]+', attempt):
    raise SystemExit('invalid attempt')
obs = here / 'observations' / ('ipra-' + attempt)
lean = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
rowlib = Path('/tmp/displayed80-rows-msc3s0w3')
lib = Path('/tmp/direct80-coherent-rebuild-2fbk3sj_/lib')
pkg = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
source = here / 'DisplayedRowsIPRA.lean'
expected = {
    lean: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    rowlib / 'DisplayedRows.olean': 'aeafe96a70f42a594e30adaf5397289b5155c98c6d481fcdf4e8bffc30956eff',
    lib / 'Direct80Graph.olean': '95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4',
    lib / 'Direct80SymbolicFixedIPRA.olean': '3fb4bd73fad0ffe1d5a57a1fbff8d1d478460f686409dafa8422d0f90dee591a',
}
def digest(p): return sha256(p.read_bytes()).hexdigest()
def need(b, message):
    if not b: raise RuntimeError(message)
def resources():
    lines = subprocess.run(['ps', '-eo', 'pid=,comm=,rss=,args='], capture_output=True, text=True, check=True).stdout.splitlines()
    processes = [x.strip() for x in lines if len(x.split(None, 3)) == 4 and x.split(None, 3)[1] == 'lean']
    memory = int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
    return {'time_ns': time.time_ns(), 'lean': processes, 'mem_available_kib': memory}
need(not obs.exists(), 'observation exists')
need(pkg.is_dir() and all(p.is_file() and digest(p) == h for p, h in expected.items()), 'missing or changed pinned provider')
pre = resources()
need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource preflight')
need(shutil.disk_usage('/tmp').free >= 4*1024**3, 'disk guard')
obs.mkdir(parents=True)
out = Path(tempfile.mkdtemp(prefix='displayed80-ipra-'))
copy = out / source.name
shutil.copyfile(source, copy)
shutil.copyfile(source, obs / 'source.txt')
source_hash = digest(source)
path = ':'.join(map(str, [rowlib, lib, pkg]))
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': path, 'LEAN_NUM_THREADS': '1'}
cmd = [str(lean), '-M3000', '-j1', '-DElab.async=false', f'--root={out}', str(copy), '-o', str(out/'DisplayedRowsIPRA.olean')]
samples, reason, start = [], None, time.monotonic()
with (obs/'stdout').open('x') as stdout, (obs/'stderr').open('x') as stderr:
    proc = subprocess.Popen(cmd, env=env, stdout=stdout, stderr=stderr)
    while proc.poll() is None:
        sample = resources(); samples.append(sample)
        if sample['mem_available_kib'] < 8*1024**2 or len(sample['lean']) > 2:
            reason = 'resource guard'; proc.terminate(); break
        if time.monotonic()-start > 300:
            reason = 'timeout'; proc.terminate(); break
        time.sleep(2)
    try: proc.wait(timeout=10)
    except subprocess.TimeoutExpired: proc.kill(); proc.wait()
output = (obs/'stdout').read_text() + (obs/'stderr').read_text()
obj = out/'DisplayedRowsIPRA.olean'
checks = {
    'inputs_unchanged': digest(source) == source_hash == digest(copy) and all(digest(p) == h for p, h in expected.items()),
    'object_exists': obj.is_file(),
    'no_diagnostics': not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)', output),
    'four_reports': len(re.findall(r'depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]', output)) == 4,
}
result = {'command': cmd, 'lean_path': path, 'exit': proc.returncode, 'reason': reason, 'output_root': str(out),
          'source_sha256': source_hash, 'runner_sha256': digest(Path(__file__)), 'pins': {str(p): h for p, h in expected.items()},
          'object_sha256': digest(obj) if obj.is_file() else None, 'stdout_sha256': digest(obs/'stdout'),
          'stderr_sha256': digest(obs/'stderr'), 'preflight': pre, 'samples': samples, 'postflight': resources(), 'checks': checks,
          'scope': 'explicit Lean rows and fixed symbolic iPRA endpoints; PDF and constants file binding remain external; provider ancestry inherited'}
(obs/'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps({'exit': proc.returncode, 'reason': reason, 'output_root': str(out), 'object_sha256': result['object_sha256'], 'checks': checks}))
need(proc.returncode == 0 and reason is None and all(checks.values()), 'Lean check failed')
