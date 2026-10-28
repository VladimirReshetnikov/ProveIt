import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REVIEWS = ROOT / 'Computability/DiophantineConsistency/reviews'
AUTHOR = REVIEWS / 'foundation-ha-peano-dependency-replay.json'
INPUTS = Path('/tmp/foundation-ha-peano-root-bhbxvn17/inputs.json')
EXPECTED_AUTHOR = '41185982ce643f8f05d928e3f0a400d9ac491d759ea68541e2914bc855071006'
EXPECTED_INPUTS = '5ed243aa5af52d8c6c3babefed3d5632441bc3b7073ca13e5666a1f8f7a77bc0'
TARGETS = {
    'DiophantineConsistency.FoundationHAPeano':
        '5785aee6255a3bd7f89f330acbdfcb818c70ae9ea0afbb6b0b656ffa3c802fed',
    'DiophantineConsistency.FoundationHAPeanoChecks':
        '023df2ef27bc5741c91a8befca19a2745f2de36111483518e1be46ac01107889',
}

def sha(path):
    return hashlib.file_digest(Path(path).open('rb'), 'sha256').hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def cache_objects(module):
    if 'objects' in module:
        return module['objects']
    return [{'path': module['object'], 'sha256': module['object_sha256']}]

require(sha(AUTHOR) == EXPECTED_AUTHOR, 'author metadata changed')
require(sha(INPUTS) == EXPECTED_INPUTS, 'author inputs changed')
author = json.loads(AUTHOR.read_text())
inputs = json.loads(INPUTS.read_text())
require(len(inputs['modules']) == 112, 'prerequisite count')
require(not (set(TARGETS) & {m['module'] for m in inputs['modules']}), 'targets in cache')
private = Path(tempfile.mkdtemp(prefix='foundation-ha-peano-controller-peer-'))
lib = private / 'lib'
lib.mkdir()
records = []
source_pins = []
for module, digest in TARGETS.items():
    path = ROOT / 'Computability/DiophantineConsistency/Lean' / (module.replace('.', '/') + '.lean')
    source_pins.append({'path': str(path), 'sha256': digest})

def authenticate():
    require(shutil.disk_usage(ROOT).free >= 512 * 1024 * 1024, 'disk reserve')
    for p in inputs['pins'] + source_pins:
        require(sha(p['path']) == p['sha256'], 'pin mismatch: ' + p['path'])
    require(sha(inputs['compiler']['path']) == inputs['compiler']['sha256'], 'compiler mismatch')
    for name, data in inputs['package_identity'].items():
        require(sha(ROOT / name) == data['current_sha256'], 'package mismatch: ' + name)
    for m in inputs['modules']:
        require(sha(m['source']) == m['source_sha256'], 'source mismatch: ' + m['module'])
        old_prefix = '/home/codex/src/Proofs/'
        if m['source'].startswith(old_prefix):
            local = ROOT / m['source'][len(old_prefix):]
            if local.exists():
                require(sha(local) == m['source_sha256'], 'current source mismatch: ' + str(local))
        for obj in cache_objects(m):
            require(sha(obj['path']) == obj['sha256'], 'object mismatch: ' + obj['path'])

authenticate()
for m in inputs['modules']:
    stem = lib / m['module'].replace('.', '/')
    stem.parent.mkdir(parents=True, exist_ok=True)
    for obj in cache_objects(m):
        suffix = Path(obj['path']).name.split('.', 1)[1]
        destination = Path(str(stem) + '.' + suffix)
        require(not destination.exists(), 'duplicate destination: ' + str(destination))
        destination.symlink_to(Path(obj['path']).resolve())
env = dict(os.environ)
env['LEAN_PATH'] = str(lib) + ':' + inputs['lean_path'].split(':', 1)[1]
require('/tmp/foundation-ha-peano-root-' not in env['LEAN_PATH'], 'author targets on path')
for module, digest in TARGETS.items():
    authenticate()
    source = Path(next(x['path'] for x in source_pins if x['sha256'] == digest))
    output = lib / (module.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log = private / (module.rsplit('.', 1)[-1] + '.log')
    snapshot = private / source.name
    snapshot.write_bytes(source.read_bytes())
    command = [inputs['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
               '-o', str(output), str(source)]
    started = time.monotonic()
    with log.open('wb') as stream:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    record = {'module': module, 'source': str(source), 'source_sha256': digest,
              'command': command, 'exit_code': result.returncode,
              'seconds': time.monotonic() - started, 'log': str(log),
              'log_sha256': sha(log), 'snapshot': str(snapshot),
              'snapshot_sha256': sha(snapshot), 'object': str(output)}
    if output.exists():
        record['object_sha256'] = sha(output)
        old = next(x for x in author['fresh_modules'] if x['module'] == module)
        record['author_object_sha256'] = old['object_sha256']
        record['byte_identical_to_author'] = record['object_sha256'] == old['object_sha256']
    records.append(record)
    (private / 'executions.json').write_text(json.dumps(records, indent=2) + '\n')
    print(module, result.returncode, record.get('byte_identical_to_author'), flush=True)
    require(result.returncode == 0, 'Lean failed; retained log: ' + str(log))
    authenticate()

text = Path(records[-1]['log']).read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
require(len(reports) == 9, 'expected nine axiom reports')
for declaration, raw_axioms in reports:
    require(set(x.strip() for x in raw_axioms.split(',')) <=
            {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axiom: ' + declaration)
require(Path(records[0]['log']).read_bytes() == b'', 'main diagnostics unexpectedly nonempty')
authenticate()
receipt = {'scope': 'Independent peer: two private fresh leaves; 112 authenticated cached prerequisites, not a fresh closure.',
           'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
           'private': str(private), 'author_metadata': str(AUTHOR),
           'author_metadata_sha256': EXPECTED_AUTHOR, 'inputs': str(INPUTS),
           'inputs_sha256': EXPECTED_INPUTS, 'prerequisites': inputs['modules'],
           'pin_observations': len(inputs['pins']), 'compiler': inputs['compiler'],
           'package_identity': inputs['package_identity'], 'lean_path': env['LEAN_PATH'],
           'fresh_modules': records, 'axiom_reports': reports,
           'authenticated_object_alternatives': inputs['authenticated_object_alternatives'],
           'driver': str(Path(__file__).resolve()), 'driver_sha256': sha(__file__)}
destination = REVIEWS / 'foundation-ha-peano-peer-replay.json'
require(not destination.exists(), 'refuse to overwrite peer metadata')
destination.write_text(json.dumps(receipt, indent=2) + '\n')
print('METADATA', destination, sha(destination), flush=True)
print('PRIVATE', private, flush=True)
