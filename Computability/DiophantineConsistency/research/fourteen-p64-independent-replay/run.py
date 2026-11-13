#!/usr/bin/env python3
"""Fresh eight-module P64 replay on the recorded captured-provider overlay."""
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1] / 'Lean' / 'DiophantineConsistency' / 'Compact44'
RESEARCH = HERE.parent
OUT = Path('/tmp/p64-independent-captured-replay')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
SOURCES = {
    'P64Graph': '24ddb2677b60a25d16981c1043cb06754e2c01ca58b8147878086abe7f65d489',
    'P64Root': 'afcbb52982e7c1334e615029e4af554fbb53c86ee07e77070212d2edf47118f9',
    'P64Norm': 'd4e7ebc1c4b969a7b74fe509011f2ccd9e486cb6c455a9e863d1d4802f7ea1b4',
    'P64Early': '4db7d2153b1849d4646503244f7a5f2df031ddbeda4f135194b836ea125a02c1',
    'P64Facts': '4edd062b84bf7b2bf131a7c3ff1a6125aa6fffc9e1ddb0ae9d5b13a60566f47a',
    'P64ConvZero': 'a830a6792c7333d3054912242dc8cab5ab3dfeeec8b9f993af895cfc3360b2e8',
    'P64Converse': 'c17a5171f2b0120dbcadd2ea2656406367f5d3945d11f8bf70a6ec6d62ccbe35',
    'IPRAPositive64': 'dee5caed605f79f4fb549692aca3b44bb5d981b1e27ac4a6ad801a01fbfb5ca0',
}
P65_SHIM_SHA = '7bd2902eeffa586418aedef1aded667be68d32c0aeb6f3946a09d277db3dc19c'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def guard_sources():
    for name, expected in SOURCES.items():
        if sha(PROJECT / (name + '.lean')) != expected:
            raise SystemExit('source drift: ' + name)
    if sha(LEAN) != LEAN_SHA or sha(Path('/tmp/P65GraphShim.olean')) != P65_SHIM_SHA:
        raise SystemExit('Lean or P65GraphShim drift')

if OUT.exists():
    raise SystemExit('refusing existing output directory: ' + str(OUT))
guard_sources()
audit = subprocess.run([sys.executable, str(RESEARCH / 'p65-post-merge-replay/audit.py')],
                       text=True, capture_output=True)
if audit.returncode:
    raise SystemExit('P65 captured-provider audit failed: ' + audit.stdout + audit.stderr)
OUT.mkdir()
(OUT / 'lib').mkdir()
(OUT / 'logs').mkdir()
subprocess.run(['cp', '-as', '/tmp/p65-post-merge-replay/lib/.', str(OUT / 'lib')], check=True)
destdir = OUT / 'src/DiophantineConsistency/Compact44'
destdir.mkdir(parents=True)
libdir = OUT / 'lib/DiophantineConsistency/Compact44'
libdir.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
paths = [str(OUT / 'lib'), '/tmp', '/tmp/trace74-direct-four-block-1zltaw2f/lib',
         '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
env['LEAN_PATH'] = ':'.join(paths)
records = []
selected = set(SOURCES)
guards = {}
for name, source_sha in SOURCES.items():
    source = PROJECT / (name + '.lean')
    text = source.read_text()
    if name == 'P64Graph':
        old = 'import DiophantineConsistency.Compact44.FreeJSumSquares\n'
        if not text.startswith(old):
            raise SystemExit('unexpected graph import')
        text = 'import P65GraphShim\n' + text[len(old):]
    shim = destdir / (name + '.lean')
    shim.write_text(text)
    obj = libdir / (name + '.olean')
    if obj.exists() or obj.is_symlink():
        raise SystemExit('unexpected existing selected object: ' + str(obj))
    imports = re.findall(r'^import\s+(\S+)', text, re.M)
    deps = {}
    for module in imports:
        rel = module.replace('.', '/') + '.olean'
        resolved = next((Path(root) / rel for root in paths if (Path(root) / rel).exists()), None)
        if resolved is None:
            raise SystemExit('unresolved direct import: ' + module)
        value = sha(resolved)
        if module.rsplit('.', 1)[-1] not in selected:
            guards[str(resolved)] = value
        deps[module] = {'path': str(resolved), 'sha256': value}
    command = [str(LEAN), '-M6000', '-j1', '-DElab.async=false',
               '--root=' + str(OUT / 'src'), str(shim), '-o', str(obj)]
    print('Building ' + name, flush=True)
    before = time.monotonic()
    try:
        done = subprocess.run(command, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=300)
        output, code = done.stdout, done.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or '')
        output += '\nTimed out after 300 seconds.\n'
        code = 124
    log = OUT / 'logs' / (name + '.txt')
    log.write_text(output)
    record = {'module': name, 'source': str(source), 'source_sha256': source_sha,
              'shim': str(shim), 'shim_sha256': sha(shim), 'imports': deps,
              'command': command, 'exit': code, 'seconds': round(time.monotonic()-before, 3),
              'log': str(log), 'log_sha256': sha(log), 'object': str(obj),
              'object_sha256': sha(obj) if obj.exists() else None}
    records.append(record)
    (OUT / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
    if code or any(s in output for s in ('sorryAx', 'error:', 'warning:')):
        print('FAILED ' + name + '\n' + output[-6000:], flush=True)
        sys.exit(1)
    guard_sources()
    for path, expected in guards.items():
        if sha(Path(path)) != expected:
            raise SystemExit('direct-provider drift: ' + path)
    for r in records:
        if sha(Path(r['object'])) != r['object_sha256']:
            raise SystemExit('rebuilt-object drift: ' + r['module'])
end = (OUT / 'logs/IPRAPositive64.txt').read_text()
for name in ('positiveBridge', 'native_equivalence', 'standard_equivalence', 'reference_equivalence'):
    if not re.search(r"'DiophantineConsistency\.IPRAPositive64\." + name +
                     r"' depends on axioms: \[propext, Classical.choice, Quot.sound\]", end):
        raise SystemExit('missing expected endpoint axiom report: ' + name)
(OUT / 'result.json').write_text(json.dumps({'status': 'PASS', 'modules': len(records),
    'lean_sha256': LEAN_SHA, 'lean_path': paths, 'direct_provider_guards': guards,
    'p65_audit': json.loads(audit.stdout), 'scope': 'captured-provider replay'}, indent=2) + '\n')
print('PASS: forced eight-module captured-provider replay', flush=True)
