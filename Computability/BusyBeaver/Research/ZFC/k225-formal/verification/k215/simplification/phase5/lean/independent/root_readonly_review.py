"""Root's independent byte review of the completed current and predecessor closures."""
from pathlib import Path
import hashlib
import json
import re

REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
RUN = Path('/tmp/k215-proof-phase5/lean-run1')
BASIS = Path('/tmp/k215-proof-phase4/lean-run1')
OUT = Path('/tmp/k215-proof-phase5/root-actual-review.json')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

assert not OUT.exists()
result = read(RUN / 'result.json')
assert result['status'] == 'PASS'
inventories = {}
for directory, expected in [(RUN, 184), (BASIS, 185)]:
    inv, done, summary = (read(directory / n) for n in ('inventory.json', 'completed.json', 'result.json'))
    assert summary['status'] == 'PASS' and len(inv['modules']) == len(done) == expected
    assert sha(directory / 'inventory.json') == summary['inventory_sha256']
    assert sha(directory / 'completed.json') == summary['completed_sha256']
    assert set(done) == {row['module'] for row in inv['modules']}
    assert inv['external_imports'] == ['Init']
    paths = list((directory / 'objects').rglob('*'))
    assert all(not p.is_symlink() or p.is_file() for p in paths)
    assert {p.relative_to(directory / 'objects').as_posix() for p in paths if p.is_file()} == {
        m.replace('.', '/') + '.olean' for m in done}
    for row in inv['modules']:
        m, rec = row['module'], done[row['module']]
        assert rec['status'] == 'PASS' and rec['source_sha256'] == row['source_sha256']
        assert rec['dependencies'] == {d: done[d]['object_sha256'] for d in row['imports'] if d in done}
        obj = directory / 'objects' / (m.replace('.', '/') + '.olean')
        assert sha(obj) == rec['object_sha256'] and sha(rec['log']) == rec['log_sha256']
        if directory == RUN:
            assert sha(row['source']) == row['source_sha256']
            if rec['origin'] == 'phase4_hash_bound':
                assert obj.is_symlink() and obj.resolve() == (BASIS / 'objects' / (m.replace('.', '/') + '.olean')).resolve()
            else:
                assert rec['origin'] == 'phase5_fresh' and not obj.is_symlink()
        else:
            assert not obj.is_symlink()
    inventories[directory] = inv
assert {r['module'] for r in inventories[BASIS]['modules']} - {r['module'] for r in inventories[RUN]['modules']} == {'BusyBeaver.ZFC.RMOffsetBisim'}
for row in read(RUN / 'toolchain.json').values():
    if isinstance(row, dict) and 'path' in row and 'sha256' in row:
        assert sha(row['path']) == row['sha256']
reports = 0
for audit in result['audits']:
    assert audit['status'] == 'PASS'
    folder = Path(audit['log']).parent
    assert sha(audit['source']) == audit['source_sha256']
    assert sha(folder / (audit['module'] + '.olean')) == audit['object_sha256']
    assert sha(audit['log']) == audit['log_sha256']
    log = Path(audit['log']).read_text()
    assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
    rs = re.findall(r'depends on axioms: \[([^]]*)\]', log)
    assert all({x.strip() for x in s.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'} for s in rs)
    reports += len(rs) + log.count('does not depend on any axioms')
assert len(result['audits']) == 2 and reports == 10
machine = REPO / 'Computability/BusyBeaver/Research/ZFC/candidate-k215'
assert sha(machine / 'k215.tm') == 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
assert sha(machine / 'k215.native.tm') == '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
assert sha(machine / 'sites215.json') == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
receipt = {'status': 'PASS_ROOT_READ_ONLY_BINDINGS', 'current_modules': 184, 'predecessor_modules': 185,
           'typed_audits': 2, 'axiom_reports': reports, 'result_sha256': sha(RUN / 'result.json'),
           'reviewer_sha256': sha(__file__), 'exact_machine_inputs_unchanged': True,
           'scope': 'Independent byte checks of current sources, both complete provider sets, dependency hashes, compiler inputs, raw logs and audit objects. No compiler or new mathematical proof.'}
OUT.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
