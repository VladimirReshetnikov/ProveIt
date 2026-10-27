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

attempts_file = Path('/tmp/control-bisim-perm215-controller-author-attempts.json')
paths = [Path(p) for p in json.loads(attempts_file.read_text())]
states = [json.loads((p / 'AUTHOR.json').read_text()) for p in paths]
assert states[-1]['status'] == 'PASS'
records = states[-1]['records']
assert len(records) == 2
assert sum(len(r['axiom_reports']) for r in records) == 11
for r in records:
    assert r['exit_code'] == 0
    for key in ['source', 'snapshot', 'object', 'log', 'timing']:
        verify(r[key])
    assert Path(r['object']['path']).is_file() and not Path(r['object']['path']).is_symlink()

out = REV / 'arithmetic-control-bisim-perm215-author-replay'
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

for f in [attempts_file, Path('/tmp/build-control-bisim-perm215-source.py'),
          Path('/tmp/control-bisim-perm215-source-audit.json'), Path(__file__)]:
    shutil.copyfile(f, out / f.name)

inputs = json.loads((paths[-1] / 'inputs.json').read_text())
import re
text = Path(records[0]['source']['path']).read_text()
initial = json.loads(Path('/tmp/control-bisim-perm215-source-audit.json').read_text())
literal = re.search(r'def packedCert : Nat := 0x([0-9a-f]+)', text)[1]
assert hashlib.sha256(literal.encode()).hexdigest() == initial['packed_hex_sha256']
packed = int(literal, 16)
assert packed < 1 << (96*2850)
entries = []
for i in range(2850):
    x = (packed >> (96*i)) % (1 << 96)
    assert x < 1 << 86
    e = [x % 8192, (x >> 13) % 8192,
         [(x >> (26+2*j)) % 4 for j in range(9)],
         [(x >> (44+2*j)) % 4 for j in range(9)], (x >> 62) % 4096, (x >> 74) % 4096]
    assert 0 < e[0] == e[1] and e[2] == e[3] == [0]*9 and e[4] < 2850 and e[5] < 2850
    entries.append(e)
assert hashlib.sha256(json.dumps(entries,separators=(',',':')).encode()).hexdigest() == initial['entries_sha256']
assert [int(n) for n in re.findall(r'private theorem block_(\d+) : block',text)] == list(range(45))
wiring = text.split('private theorem blocks_checked',1)[1].split('/-- Every actual',1)[0]
assert [int(n) for n in re.findall(r'Fin.cases block_(\d+)',wiring)] == list(range(45))
for st in states:
    snap = Path(st['records'][0]['snapshot']['path']).read_text()
    assert re.search(r'def packedCert : Nat := 0x([0-9a-f]+)',snap)[1] == literal
save(out/'final-data-audit.json',dict(final_source=records[0]['source'],final_checks=records[1]['source'],
    initial_audit=rec(out/'control-bisim-perm215-source-audit.json'), entries=2850,
    complete_blocks=45,final_block_entries=34,all_slots_roundtrip=True,
    all_entries_diagonal_and_explicit_zero_vectors=True,all_reserved_high_bits_zero=True,
    whole_packed_high_bits_zero=True,entry_sha256=initial['entries_sha256'],
    packed_hex_sha256=initial['packed_hex_sha256'],all_attempt_literals_identical=True))
save(out / 'freeze-authentication.json', dict(observations=observations, distinct_original_paths=len(unique), pins=list(unique.values())))
packet = dict(
    status='PASS',
    scope='Complete actual 2,850-entry kernel certificate and internal DagPerm/p215 control halting equivalence from every internal register file in every IΣ1 model. No Turing simulation, source-ZFC calibration, or HA equivalence.',
    counts=states[-1]['counts'], records=records,
    attempts=[rec(out / f'attempt{i}' / 'AUTHOR.json') for i in range(1, len(paths) + 1)],
    final_inputs=rec(out / f'attempt{len(paths)}' / 'inputs.json'),
    authentication=rec(out / 'freeze-authentication.json'),
    source_audit=rec(out / 'control-bisim-perm215-source-audit.json'), final_data_audit=rec(out / 'final-data-audit.json'),
    generator=rec(out / 'build-control-bisim-perm215-source.py'),
    final_private=str(paths[-1]),
    provider_supplement=inputs['provider_supplement'], accepted_table_supplement=inputs['accepted_table_supplement'],
    original_plan=inputs['cache'],
    compiler=inputs['compiler'], LEAN_PATH=inputs['LEAN_PATH'],
    driver=rec(out / f'attempt{len(paths)}' / 'driver.py'),
    source_review='Full main, Checks and executed driver read before each compile. Full packed literal reconstructed and all 2,850 slots round-tripped; every entryOK/shape/reserved-bit check is kernel proved. First failed attempt only lacked explicit Decidable instance, with unchanged mathematical statements and data.',
)
packetpath = REV / 'arithmetic-control-bisim-perm215-replay.json'
assert not packetpath.exists()
save(packetpath, packet)
manifest = [dict(path=str(p.relative_to(R)), sha256=rec(p)['sha256'], bytes=p.stat().st_size)
            for p in sorted(out.rglob('*')) if p.is_file()]
save(out / 'FILES.json', manifest)
for p in [packetpath, out / 'FILES.json']:
    print(rec(p)['sha256'], p)
print('files', len(manifest), 'observations', observations, 'distinct paths', len(unique))
