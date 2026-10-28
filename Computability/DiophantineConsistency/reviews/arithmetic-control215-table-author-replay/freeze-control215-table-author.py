from pathlib import Path
import hashlib, json, shutil

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = R / 'Computability/DiophantineConsistency/reviews'

def rec(p):
    p = Path(p)
    return dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest(), bytes=p.stat().st_size)

def save(p, value):
    Path(p).write_text(json.dumps(value, indent=2) + '\n')

def verify(r):
    assert rec(r['path'])['sha256'] == r['sha256'], r['path']

attempts_file = Path('/tmp/control215-table-controller-author-attempts.json')
paths = [Path(p) for p in json.loads(attempts_file.read_text())]
states = [json.loads((p / 'AUTHOR.json').read_text()) for p in paths]
assert states[-1]['status'] == 'PASS'
records = states[-1]['records']
assert len(records) == 2
assert sum(len(r['axiom_reports']) for r in records) == 9
for r in records:
    assert r['exit_code'] == 0
    for key in ['source', 'snapshot', 'object', 'log', 'timing']:
        verify(r[key])
    assert Path(r['object']['path']).is_file() and not Path(r['object']['path']).is_symlink()

out = REV / 'arithmetic-control215-table-author-replay'
assert not out.exists()
out.mkdir()
observations = 0
unique = {}
for ix, (p, st) in enumerate(zip(paths, states), 1):
    dest = out / f'attempt{ix}'
    dest.mkdir()
    for name in ['AUTHOR.json', 'inputs.json', 'driver.py']:
        if (p / name).exists():
            shutil.copyfile(p / name, dest / name)
    if (p / 'inputs.json').exists():
        inputs = json.loads((p / 'inputs.json').read_text())
        for pin in inputs['pins']:
            verify(pin)
            unique[pin['path']] = pin
            observations += 1
        for mod in inputs['modules']:
            for pin in [mod['source'], *mod['objects']]:
                verify(pin)
                unique[pin['path']] = pin
                observations += 1
        for provider in inputs['actual_providers']:
            verify(provider['actual'])
            observations += 1
    for row in st['records']:
        verify(row['snapshot'])
        assert row['snapshot']['sha256'] == row['source']['sha256']
        for key in ['snapshot', 'object', 'log', 'timing']:
            if key in row:
                pin = row[key]
                verify(pin)
                shutil.copyfile(pin['path'], dest / Path(pin['path']).name)

for f in [attempts_file, Path('/tmp/build-control215-table-source.py'),
          Path('/tmp/control215-table-source-audit.json'), Path(__file__)]:
    shutil.copyfile(f, out / f.name)

inputs = json.loads((paths[-1] / 'inputs.json').read_text())
save(out / 'freeze-authentication.json', dict(observations=observations, distinct_original_paths=len(unique), pins=list(unique.values())))
packet = dict(
    status='PASS',
    scope='Complete actual p215 packed control catalogue, all 4,751 rows and high-bit bound, with internal represented run and instruction specification. No DagPerm bisimulation, Turing simulation, source-ZFC calibration, or HA equivalence.',
    counts=states[-1]['counts'], records=records,
    attempts=[rec(out / f'attempt{i}' / 'AUTHOR.json') for i in range(1, len(paths) + 1)],
    final_inputs=rec(out / f'attempt{len(paths)}' / 'inputs.json'),
    authentication=rec(out / 'freeze-authentication.json'),
    source_audit=rec(out / 'control215-table-source-audit.json'),
    generator=rec(out / 'build-control215-table-source.py'),
    final_private=str(paths[-1]),
    provider_supplement=inputs['provider_supplement'],
    original_plan=inputs['cache'],
    compiler=inputs['compiler'], LEAN_PATH=inputs['LEAN_PATH'],
    driver=rec(out / f'attempt{len(paths)}' / 'driver.py'),
    source_review='Full main, Checks and executed driver read before each compile. Full packed literal reconstructed and all 4,751 slots round-tripped; kernel checks establish the theorem.',
)
packetpath = REV / 'arithmetic-control215-table-replay.json'
assert not packetpath.exists()
save(packetpath, packet)
manifest = [dict(path=str(p.relative_to(R)), sha256=rec(p)['sha256'], bytes=p.stat().st_size)
            for p in sorted(out.rglob('*')) if p.is_file()]
save(out / 'FILES.json', manifest)
for p in [packetpath, out / 'FILES.json']:
    print(rec(p)['sha256'], p)
print('files', len(manifest), 'observations', observations, 'distinct paths', len(unique))
