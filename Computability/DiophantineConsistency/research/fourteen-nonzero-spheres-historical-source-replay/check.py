#!/usr/bin/env python3
"""Replay unchanged historical auditor with two authenticated Git blobs, in memory."""
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import resource
import subprocess
import sys

if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):
    raise SystemExit('use python3 -I -S -B without optimization')
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
resource.setrlimit(resource.RLIMIT_CPU, (50, 50))
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
HERE = Path(__file__).resolve().parent
TASK = HERE.parents[1]
ROOT = TASK.parents[1]
OLD = 'a9bba4836516478cc5a052b9986662de628ac320'
NEW = '79ddf75e93efa7b8c83600e64651479cfd7dc4e7'
BASE = 'Computability/DiophantineConsistency/'
AUDIT = TASK / 'research/fourteen-nonzero-spheres/audit.py'
AUDIT_SHA = 'f4b11d8b001d3f32ff0151d1f4871667ce638ef552b0141a222487ce1ceb08ce'
PAIR = {
    'CarrierScaledAuxiliary118': ('2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620', '174c685cf1669080cccb3760a10317aff0c99bc439bf8070eeed525ec37bff04'),
    'CarrierNonzeroSpheres': ('f2fb2bfc613e152e9b62d690d1564b41735f34dd2f7ec71c1a5980212b4ed51a', '481f68dd519db210d2b81dd2756002e2bfecbf4744f03f143051c8f029ecebe9'),
}
DIFF_SHA = 'fd4d42196d64682d97679dc59bd140c0df9f5cf8497bdff3db88ea497114af66'
def need(b, why):
    if not b:
        raise RuntimeError(why)
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args):
    return subprocess.run(['git', '-C', str(ROOT), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout

need(sha(AUDIT.read_bytes()) == AUDIT_SHA, 'historical auditor bytes changed')
need(git('show', OLD + ':' + BASE + 'research/fourteen-nonzero-spheres/audit.py') == AUDIT.read_bytes(), 'auditor historical provenance')
files = [BASE + 'Lean/DiophantineConsistency/' + n + '.lean' for n in PAIR]
diff = git('diff', '--no-ext-diff', '--no-renames', OLD, NEW, '--', *files)
need(sha(diff) == DIFF_SHA, 'reviewed source diff changed')
old_blobs = {}
new_blobs = {}
for (name, (old_sha, new_sha)), rel in zip(PAIR.items(), files):
    old, new = git('show', OLD + ':' + rel), git('show', NEW + ':' + rel)
    need(sha(old) == old_sha and sha(new) == new_sha, 'blob hash ' + name)
    current = (ROOT / rel).read_bytes()
    need(current == new, 'tracked source differs from reviewed new blob: ' + name)
    old_blobs[(ROOT / rel).resolve()] = (old_sha, old)
    new_blobs[name] = (old.decode(), new.decode())

old, new = new_blobs['CarrierScaledAuxiliary118']
old_hb = ('  have hb : (0 : ℤ)<CurrentWindowCarry2011.ports 0 := by\n'
          '    change (0 : ℤ)<CurrentMasks2011.beta\n'
          '    exact_mod_cast CurrentMasks2011.beta_pos\n')
new_hb = ('  have hb : (0 : ℤ)<CurrentWindowCarry2011.ports 0 := '
          'CurrentMasks2011.beta_pos_int\n')
need(old.count(old_hb) == 1 and old.replace(old_hb, new_hb, 1) == new,
     'scaled source changes outside local positivity proof')
old, new = new_blobs['CarrierNonzeroSpheres']
start = 'theorem current_positive_zero71_iff'
end = '/-- External exact-current-port equivalences'
need(old.split(start,1)[0] == new.split(start,1)[0] and
     old.split(end,1)[1] == new.split(end,1)[1], 'sphere source outside endpoint blocks')
for name in ('current_positive_zero71_iff', 'current_positive_zero72_iff'):
    def statement(source):
        return source.split('theorem '+name,1)[1].split(':= by',1)[0]
    need(statement(old) == statement(new), 'changed endpoint statement: ' + name)

spec = importlib.util.spec_from_file_location('historical_sphere_audit', AUDIT)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
real_pinned = module.pinned
used = set()
def pinned_with_historical_blobs(path, digest):
    resolved = path.resolve()
    if resolved in old_blobs:
        expected, raw = old_blobs[resolved]
        need(digest == expected and sha(raw) == digest, 'intercepted pin mismatch')
        need(resolved not in used, 'duplicate interception')
        used.add(resolved)
        return raw
    return real_pinned(path, digest)
module.pinned = pinned_with_historical_blobs
out = io.StringIO()
sys.argv = [str(AUDIT)]
with contextlib.redirect_stdout(out):
    module.main()
need(used == set(old_blobs), 'expected interceptions not reached')
result = json.loads(out.getvalue())
need(result['status'] == 'PASS', 'historical audit did not pass')
print(json.dumps({
    'auditor_sha256': AUDIT_SHA,
    'original_commit': OLD,
    'reviewed_current_commit': NEW,
    'reviewed_git_diff_sha256': DIFF_SHA,
    'historical_git_blob_substitutions': {name: {'historical_sha256': a, 'current_sha256': b} for name, (a,b) in PAIR.items()},
    'historical_auditor_result': result,
    'other_pins_verified_by_unchanged_historical_auditor': True,
    'historical_certificate_compared_byte_for_byte': True,
    'reviewed_diff_confined_to_endpoint_proof_bodies': True,
    'current_lean_providers_revalidated': False,
    'lean_or_build_executed': False,
    'review_scope': 'Historical finite graph/degree/port audit with two in-memory Git blobs; no current Lean proof-provider validation.'
}, indent=2, sort_keys=True))
