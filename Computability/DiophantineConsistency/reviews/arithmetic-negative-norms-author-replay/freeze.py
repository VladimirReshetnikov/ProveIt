from pathlib import Path
import hashlib, json, os, re, shutil

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
REV = DC / 'reviews'
BUNDLE = REV / 'arithmetic-negative-norms-author-replay'
PACKET = REV / 'arithmetic-negative-norms-replay.json'
observations = []
attempt_objects = []


def require(ok, message):
    if not ok: raise RuntimeError(message)


def record(path):
    path = Path(path); data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2)+'\n')


def check(expected, actual=None):
    found = record(actual or expected['path'])
    require(found['sha256'] == expected['sha256'], 'hash '+expected['path'])
    require('bytes' not in expected or found['bytes'] == expected['bytes'], 'size '+expected['path'])
    observations.append(dict(expected=expected, actual=found))
    return found


def copy(source, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    require(not destination.exists(), 'new destination '+str(destination))
    # Every source here is immutable terminal-attempt evidence or a frozen plan.
    # Hardlinks preserve regular-file paths and exact bytes without another copy.
    os.link(source, destination)
    require(destination.is_file() and not destination.is_symlink(), 'regular evidence')
    check(record(source), destination)


paths = [Path(p) for p in Path('/tmp/arithmetic-negative-norms-author-runs.txt').read_text().splitlines()]
require(len(paths) == 3, 'three complete attempts')
states = [json.loads((p/'state.json').read_text()) for p in paths]
require(all(s['status'] == 'FAILED' for s in states[:-1]) and states[-1]['status'] == 'PASS', 'chronology')
require(shutil.disk_usage('/tmp').free >= 512*1024**2+32*1024**2, 'freeze reserve')
require(not BUNDLE.exists() and not PACKET.exists(), 'new frozen evidence')
BUNDLE.mkdir()
for index, (private, state) in enumerate(zip(paths, states), 1):
    inputs = json.loads((private/'inputs.json').read_text())
    authentication = json.loads((private/'authentication.json').read_text())
    providers = json.loads((private/'providers.json').read_text())
    source_paths = {x['path'] for x in inputs['sources']}
    for source in inputs['sources']:
        check(source, private/'logs'/Path(source['path']).name)
    for pin in authentication['pins']:
        check(pin, private/'logs'/Path(pin['path']).name if pin['path'] in source_paths else None)
    require(len(providers) == 455, 'complete provider set')
    for provider in providers:
        check(provider['expected']); check(provider['actual'])
    check(state['inputs']); check(state['driver'], private/'driver.py')
    for row in state['records']:
        for key in ['snapshot', 'log', 'timing']: check(row[key])
        if 'object' in row: check(row['object'])
    for source in inputs['sources']:
        output = private/'lib'/'DiophantineConsistency'/(Path(source['path']).stem+'.olean')
        if output.exists():
            require(output.is_file() and not output.is_symlink(), 'regular attempt output')
            attempt_objects.append(dict(attempt=index, object=check(record(output))))
    for name in ['state.json', 'inputs.json', 'authentication.json', 'providers.json', 'driver.py']:
        copy(private/name, BUNDLE/f'attempt-{index}'/name)
    for source in sorted((private/'logs').iterdir()):
        copy(source, BUNDLE/f'attempt-{index}'/source.name)

final = states[-1]; private = paths[-1]
inputs = json.loads((private/'inputs.json').read_text())
require(inputs['counts'] == dict(custom=86, Foundation=86, artifacts=344, external=37,
    boundary_artifacts=111, boundary_primaries=37, boundary_companions=74,
    actual_first_providers=455, fresh_prerequisites=0), 'exact approved profile')
require(len(final['records']) == 2 and len(final['records'][1]['axiom_reports']) == 7, 'seven reports')
for row in final['records']:
    check(row['source']); check(row['object']); require(row['exit_code'] == 0, 'exit zero')
    require(not re.search(r'\b(?:warning|error|sorryAx)\b', Path(row['log']['path']).read_text()), 'clean log')
    row['peak_rss_kib'] = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',
        Path(row['timing']['path']).read_text()).group(1))
for theorem, axioms in final['records'][1]['axiom_reports']:
    require(set(x.strip() for x in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'},
        'standard axioms '+theorem)
copy(Path(inputs['plan']['path']), BUNDLE/'plan.json')
copy(Path(inputs['proposal']['path']), BUNDLE/'proposal.md')
copy(Path(__file__), BUNDLE/'freeze.py')
save(BUNDLE/'freeze-authentication.json', dict(observations=observations,
    count=len(observations), unique_paths=len({x['actual']['path'] for x in observations})))
manifest = [record(p) for p in sorted(BUNDLE.rglob('*')) if p.is_file()]
for item in manifest: item['path'] = str(Path(item['path']).relative_to(ROOT))
save(BUNDLE/'FILES.json', manifest)
require(shutil.disk_usage('/tmp').free >= 512*1024**2, 'final freeze reserve')
packet = dict(status='PASS', author='complemented47_review',
    scope='Every internal IΣ1 arithmetic model: actual square residues modulo four exclude x*x+t*t+1=A*A*t*t for all A,x,t, including A=0/1 and t=0. The consecutive-product negative norm x*x+1=n*(n+1)*y*y is excluded for n>=2 by genuine bounded order induction on y. The inverse ordinate is positive and strictly smaller; the root is an absolute difference and receives no sign premise. Actual main, strong and square-coefficient auxiliary exclusions follow. Checks retain the explicit n=x=y=1 counterexample. No standardness/sign oracle, external Pell classification, source/index premise, signed-pair product extraction, literal splitNatural evaluator binding or final polynomial/PA/HA endpoint.',
    counts=inputs['counts'],
    attempts=[dict(private=str(p), status=s['status'], state=record(p/'state.json'),
        durable=record(BUNDLE/f'attempt-{i}'/'state.json'))
        for i, (p,s) in enumerate(zip(paths,states),1)],
    attempt_objects=attempt_objects, records=final['records'], private_provider=str(private/'lib'),
    final_state=record(private/'state.json'), plan=inputs['plan'], scope_supplement=inputs['proposal'],
    inputs=record(private/'inputs.json'), providers=record(private/'providers.json'),
    authentication=record(private/'authentication.json'),
    freeze_authentication=record(BUNDLE/'freeze-authentication.json'), manifest=record(BUNDLE/'FILES.json'),
    driver=final['driver'], compiler=inputs['compiler'], LEAN_PATH=inputs['LEAN_PATH'],
    first_provider_artifacts=455, final_observed_paths=final['final_observed_paths'],
    final_free_bytes=final['final_free_bytes'], freeze_free_bytes=shutil.disk_usage('/tmp').free,
    failed_attempts=2, evidence_storage='Regular hardlinks to immutable terminal-attempt evidence and frozen plan/proposal/driver bytes; new manifests and authentication are ordinary newly written files. No source or proof object is rewritten.',
    history='All three attempts preserve both input snapshots, driver, exact commands, full logs/timings, state and complete pins/provider evidence. Attempts1 and2 did not compile Checks, whose snapshots are retained. Attempt1 rejected a missing noncomputable annotation for the private magnitude helper, with resulting simplifier errors and three linter notices. Attempt2 rejected only associative/commutative normalization in the second order branch of the magnitude-square identity. Attempt3 adds the missing AC rewrite lemmas and passes both leaves. No mathematical statement, assumption, import or resource limit changed; no dependency refresh. All proof/Checks/driver bytes were fully read before each compiler. Immutable inventory/proposal references avoid redundant per-attempt copies.')
save(PACKET, packet)
print(json.dumps(dict(packet=record(PACKET), manifest=record(BUNDLE/'FILES.json'), files=len(manifest),
    freeze_observations=len(observations), freeze_paths=len({x['actual']['path'] for x in observations}),
    records=final['records'], free_bytes=shutil.disk_usage('/tmp').free), indent=2))
