"""Root's independent byte review of the completed current and predecessor closures."""
from pathlib import Path
import hashlib
import json
import re

REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
RUN = Path('/tmp/k215-proof-phase8/lean-run1')
BASIS = Path('/tmp/k215-proof-phase7/lean-run1')
OUT = Path('/tmp/k215-proof-phase8/root-actual-review.json')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

assert not OUT.exists()
result = read(RUN / 'result.json')
assert result['status'] == 'PASS'
inventories = {}
for directory, expected in [(RUN, 188), (BASIS, 187)]:
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
            if rec['origin'] == 'phase7_hash_bound':
                assert obj.is_symlink() and obj.resolve() == (BASIS / 'objects' / (m.replace('.', '/') + '.olean')).resolve()
            else:
                assert rec['origin'] == 'phase8_fresh' and not obj.is_symlink()
    inventories[directory] = inv
oldset = {r['module'] for r in inventories[BASIS]['modules']}
newset = {r['module'] for r in inventories[RUN]['modules']}
assert newset - oldset == {'BusyBeaver.ZFC.DominatedImplication'} and oldset < newset
oldrows={r['module']:r for r in inventories[BASIS]['modules']}
assert {r['module'] for r in inventories[RUN]['modules'] if r['module'] in oldrows and r['source_sha256']!=oldrows[r['module']]['source_sha256']} == {'BusyBeaver.ZFC.DomRho8', 'BusyBeaver.ZFC.KSeed222', 'BusyBeaver.ZFC.KSeedModel222'}
assert sha(BASIS / 'result.json') == '0f66683395fe36bfa450eb2525bd2e714bb804faf51bd830cfbe7b1bf0c223e9'
for row in read(RUN / 'toolchain.json').values():
    if isinstance(row, dict) and 'path' in row and 'sha256' in row:
        assert sha(row['path']) == row['sha256']
reports = 0
old_audits = {r['module']: r for r in read(BASIS / 'result.json')['audits']}
for audit in result['audits']:
    assert audit['status'] == 'PASS'
    folder = Path(audit['log']).parent
    assert sha(audit['source']) == audit['source_sha256'] == old_audits[audit['module']]['source_sha256']
    assert audit['dependencies'] == {m: r['object_sha256'] for m, r in read(RUN / 'completed.json').items()}
    assert sha(folder / (audit['module'] + '.olean')) == audit['object_sha256']
    assert sha(audit['log']) == audit['log_sha256']
    log = Path(audit['log']).read_text()
    assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
    rs = re.findall(r'depends on axioms: \[([^]]*)\]', log)
    assert all({x.strip() for x in s.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'} for s in rs)
    names = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)
    expected = {
      'EndpointAudit215': ['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation','EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
      'K215Audit': ['SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation','SetTheory.BusyBeaver.ZFC.KEndpoint215.nonhalting_iff_zfc_consistency','SetTheory.BusyBeaver.ZFC.KDense215.commutes','SetTheory.BusyBeaver.ZFC.KBoot215.boot','SetTheory.BusyBeaver.ZFC.KSites215.covered','SetTheory.BusyBeaver.ZFC.KEndpoint215.p215_boot_iff','K215Audit.blank_halts_exact','K215Audit.nonhalting_exact']}[audit['module']]
    assert [n for n,_ in names] == expected
    assert sha(folder / (audit['module'] + '.lean')) == audit['source_sha256']
    reports += len(names)
assert len(result['audits']) == 2 and reports == 10
machine = REPO / 'Computability/BusyBeaver/Research/ZFC/candidate-k215'
assert sha(machine / 'k215.tm') == 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
assert sha(machine / 'k215.native.tm') == '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
assert sha(machine / 'sites215.json') == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
owner = read(RUN/'owner.json')
for name,key in [('build.py','script_sha256'),('reviewed-driver.py','helper_sha256'),('gates.py','gates_sha256'),('basis-reference.json','basis_reference_sha256')]:
    assert sha(RUN/name) == owner[key]
for key,name in [('basis_result_sha256','result.json'),('basis_inventory_sha256','inventory.json'),('basis_completed_sha256','completed.json'),('basis_toolchain_sha256','toolchain.json')]:
    assert sha(BASIS/name) == owner[key]
reference=read(RUN/'basis-reference.json')
for name,pin in reference['files'].items():
    path=REPO/reference['repository_relative_directory']/name
    assert sha(path)==pin['sha256'] and path.stat().st_size==pin['bytes']
registration = read(RUN / 'registered-adoption.json')
assert sha(RUN/'registered-adoption.json') == result['adoption_sha256']
assert len(registration['files']) == 9
for row in registration['files']:
    source = REPO / row['destination']
    snapshot = RUN/'adopted-sources'/row['destination']
    assert sha(source) == sha(snapshot) == row['sha256']
    assert source.stat().st_size == row['bytes']
assert result['fresh_modules'] + result['reused_modules'] == 188
receipt = {'status': 'PASS_ROOT_READ_ONLY_BINDINGS', 'current_modules': 188, 'predecessor_modules': 187,
           'typed_audits': 2, 'axiom_reports': reports, 'result_sha256': sha(RUN / 'result.json'),
           'reviewer_sha256': sha(__file__), 'exact_machine_inputs_unchanged': True,
           'scope': 'Independent byte checks of current sources, both complete provider sets, dependency hashes, compiler inputs, raw logs and audit objects. No compiler or new mathematical proof.'}
OUT.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
