"""Root-owned serial proof of the remaining exact240 initialization blocks."""
from pathlib import Path
import hashlib, json, subprocess, time

B = Path('/tmp/zfc-rotation240-bootstrap')
OUT = B/'batch2-9-run1'
GEN = B/'bootstrap-plan/generate-v1.py'
BIND = B/'bootstrap-plan/prepare_continuation_guard.py'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(GEN) == '8498a6844c6aa0e3003105d523f982171107fd7d3a578e80491c03896a7a03ed'
assert sha(BIND) == '445f2abff9713b15f0cac03c3b1a4c9ca6d192f1f233276891a07f50a0d0dabf'
assert sha(B/'bootstrap-plan/check-continuation-template.py') == '1304061481be062e8fb775916d316fc696ab54e0964646298de5e3cd40edb379'
previous = B/'chunk001'
assert sha(previous/'run1/verification.json') == '1d8065f7715e8bb4e2d42bfd277a45ce64520cbf5b8fd4e6fbfafe5273c93f59'
schedule = [[14,14,14,14]]*5 + [[14,14,14,13], [12,11,10,6], [4,3,1,0]]
assert 17408 + sum(2**d for depths in schedule for d in depths) == 409691
assert not OUT.exists()
OUT.mkdir()
record = dict(status='RUNNING', start=17408, target=409691,
              scope='Exact blank initialization only; runtime frame, decoder coverage and consistency/PA endpoints remain separate.',
              schedule=schedule, commands=[], units=[])
def save():
    (OUT/'batch.json').write_text(json.dumps(record, indent=2)+'\n')
def run(index, phase, command):
    log = OUT/f'{index:03d}-{phase}.log'
    record.update(active_unit=index, active_phase=phase)
    save()
    start = time.monotonic()
    with log.open('w') as stream:
        p = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    record['commands'].append(dict(unit=index, phase=phase, command=command,
        seconds=time.monotonic()-start, exit_code=p.returncode, log=str(log), log_sha256=sha(log)))
    save()
    assert p.returncode == 0, (index, phase, log.read_text())
save()
try:
    for index, depths in enumerate(schedule, start=2):
        unit = B/f'chunk{index:03d}'
        assert not unit.exists(), unit
        prev = previous/'run1/verification.json'
        assert json.loads(prev.read_text())['status'] == 'PASS'
        run(index, 'generate', ['python3','-B',str(GEN),'--fast-evidence',str(B/'fast/run1/verification.json'),
            '--kind','next','--previous-record',str(prev),'--previous-inventory',str(previous/'source-inventory.json'),
            '--depths', *map(str,depths),'--output',str(unit)])
        run(index, 'bind', ['python3','-B',str(BIND),'--unit',str(unit)])
        run(index, 'prepare', ['python3','-B',str(unit/'check.py'),'--prepare-only','--output',str(unit/'prepared1')])
        run(index, 'actual', ['python3','-B',str(unit/'check.py'),'--output',str(unit/'run1')])
        actual = unit/'run1/verification.json'
        r = json.loads(actual.read_text())
        inventory = json.loads((unit/'source-inventory.json').read_text())
        assert r['status'] == 'PASS' and not r['prepare_only'] and r['warnings'] == 0
        assert r['before'] == r['after'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit']
        assert (r['named_axiom_probes'],r['callers']) == (len(inventory['probes']),inventory['callers'])
        row = dict(unit=index, endpoint=inventory['endpoint'], path=str(actual), sha256=sha(actual),
            probes=r['named_axiom_probes'],callers=r['callers'],
            source_seconds=r['commands'][0]['seconds'],audit_seconds=r['commands'][1]['seconds'])
        record['units'].append(row)
        previous = unit
        save()
        print(json.dumps(row),flush=True)
    assert record['units'][-1]['endpoint'] == 409691
    record.update(status='PASS_EXACT_409691_PREFIX',active_unit=None,active_phase=None)
except BaseException as ex:
    record.update(status='FAIL',error=repr(ex))
    save()
    raise
save()
print(OUT/'batch.json',flush=True)
