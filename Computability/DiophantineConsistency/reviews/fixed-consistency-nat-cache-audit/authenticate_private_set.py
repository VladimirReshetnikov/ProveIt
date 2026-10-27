"""Read-only five historical source/object audits; never compile/copy providers."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
F = Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
COMPILER = '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

records = {
    'Foundation.FirstOrder.SetTheory.Basic.Misc': '/tmp/zfc-model-coded-set-axioms/run4/verification.json',
    'Foundation.FirstOrder.SetTheory.Basic.Axioms': '/tmp/zfc-model-coded-set-axioms/run4/verification.json',
    'Foundation.FirstOrder.SetTheory.Basic.Model': '/tmp/zfc-foundation-z-route/model/run2/verification.json',
    'Foundation.FirstOrder.SetTheory.Basic': '/tmp/zfc-foundation-z-route/next/basic/run1/verification.json',
    'Foundation.FirstOrder.SetTheory.Z': '/tmp/zfc-foundation-z-route/next/z/run1/verification.json',
}
require(sha(COMPILER) == COMPILER_SHA, 'compiler changed')
# This later receipt pins all companions, explicitly distinguishing the first two.
later_path = Path(records['Foundation.FirstOrder.SetTheory.Z'])
later = json.loads(later_path.read_text())
rows = []
for module, record_path in records.items():
    record = json.loads(Path(record_path).read_text())
    require(record['status'] == 'PASS', f'{module}: not PASS')
    require(record['compiler']['sha256'] == COMPILER_SHA, f'{module}: compiler hash')
    require('4.32.0' in record['compiler']['version'], f'{module}: compiler version')
    fresh = next(r for r in record['fresh_modules'] if r['module'] == module)
    source = F / (module.replace('.', '/') + '.lean')
    require(sha(source) == fresh['source_sha256'], f'{module}: current source mismatch')
    require(sha(fresh['path']) == fresh['sha256'], f'{module}: object mismatch')
    commands = [r for r in record['commands']
                if '-o' in r['command'] and
                r['command'][r['command'].index('-o') + 1] == fresh['path']]
    require(len(commands) == 1, f'{module}: missing/ambiguous source command')
    command = commands[0]
    require(command['exit_code'] == 0, f'{module}: failed command')
    require(command['command'][0] == COMPILER, f'{module}: wrong executed compiler')
    snapshots = [p for p in command['command'] if p.endswith('.lean')]
    require(len(snapshots) == 1, f'{module}: ambiguous snapshot')
    require(sha(snapshots[0]) == fresh['source_sha256'], f'{module}: snapshot mismatch')
    log = None
    if 'log' in command:
        require(sha(command['log']) == command['log_sha256'], f'{module}: log mismatch')
        log = {'path': command['log'], 'sha256': command['log_sha256']}
    else:
        require('output' in command, f'{module}: no captured output')
        log = {'inline_output': command['output']}
    require(record.get('only_standard_axioms') is True, f'{module}: axiom audit not PASS')
    if 'source_pass_artifacts' in record:
        artifacts = record['source_pass_artifacts']
        scope = 'All four artifact hashes historically captured before audit.'
    else:
        reused = next(r for r in later['reused_modules'] if r['module'] == module)
        artifacts = reused['artifacts']
        scope = reused['artifact_scope']
    require(len(artifacts) == 4, f'{module}: missing companions')
    for artifact in artifacts:
        require(sha(artifact['path']) == artifact['sha256'], f'{module}: companion mismatch')
    rows.append({
        'module': module, 'source': str(source), 'source_sha256': sha(source),
        'record': {'path': record_path, 'sha256': sha(record_path)},
        'snapshot': {'path': snapshots[0], 'sha256': sha(snapshots[0])},
        'object': fresh['path'], 'object_sha256': fresh['sha256'],
        'compiler': record['compiler'], 'source_command': command, 'log': log,
        'objects': artifacts, 'artifact_provenance_scope': scope,
        'later_companion_record': {'path': str(later_path), 'sha256': sha(later_path)},
        'status': 'CURRENT_SOURCE_AND_HISTORICALLY_EXECUTED_OLEAN_AUTHENTICATED',
    })
result = {
    'status': 'FIVE_CURRENT_SOURCE_HISTORICAL_EXECUTED_PAIRS_PASS_NO_BUILD',
    'scope': 'No historical driver or proof source executed. Compiler/current source/snapshot/recorded successful source command/object/captured log checked. Three Model/Basic/Z bundles have four historically captured artifacts; Misc/Axioms have historically captured oleans and later-observed companions. Dependency-closure refresh is separate.',
    'driver': {'path': str(Path(__file__).resolve()), 'sha256': sha(__file__)},
    'modules': rows,
}
(HERE / 'private-set-theory-auth.json').write_text(json.dumps(result, indent=2) + '\n')
print('PASS: five current-source historical executed pairs; companion provenance retained')
