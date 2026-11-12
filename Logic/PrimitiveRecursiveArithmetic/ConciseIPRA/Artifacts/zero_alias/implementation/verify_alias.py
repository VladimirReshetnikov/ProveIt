"""Reproduce the zero-alias checker metrics, transformations and tests."""
from pathlib import Path
import ast
import concurrent.futures
import copy
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}

def metric(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = ast.unparse(tree) + '\n'
    return dict(file=str(path.relative_to(ROOT)),
                tokens=sum(t.type not in SKIP for t in
                           tokenize.generate_tokens(io.StringIO(normalized).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                normalized_bytes=len(normalized.encode()),
                source_sha256=hashlib.sha256(raw).hexdigest())

def structural_audit():
    old = (ROOT / 'ref/immediate_application/code/checker637.py').read_text()
    changed = old.replace(
        'v <= (d % 2 and (not a or a > 1 == a % 2))',
        'v <= d % 2 & a').replace(
        'c([0], q(), v=1)', 'c([0, [1, 0]], q(), v=1)').replace(
        "not str(p).strip('0123456789-[], ') and p.pop",
        "str(p).strip('0123456789-[], ') or p.pop")
    tree = ast.parse(changed)
    anonymous = tree.body[1].value
    membership, comprehension = anonymous.body.values
    binder = membership.left.func
    install_opener = ast.Assign(targets=[binder.target], value=binder.value)
    membership.left.func = ast.Name(id='i', ctx=ast.Load())
    membership.ops = [ast.NotIn()]
    generator = comprehension.generators[0]
    read_packet = ast.Assign(targets=[generator.target], value=generator.iter.elts[0])
    tree.body[1] = ast.FunctionDef(
        name='c', args=anonymous.args,
        body=[install_opener, ast.If(test=membership,
              body=[read_packet, ast.Expr(value=comprehension.elt)], orelse=[])],
        decorator_list=[], returns=None, type_comment=None)
    source = ast.unparse(ast.fix_missing_locations(tree)).replace(
        'c(g, m, k, (v := 0)) and m * 3',
        'c(g, m, k, (v := 0)) or m * 3')
    expected = ast.dump(ast.parse(source))
    actual = ast.dump(ast.parse((ROOT / 'alias_inverted.py').read_text()))
    if expected != actual:
        raise AssertionError('Candidate has changes beyond the documented transformations')
    return dict(exact_ast_transformation=True,
                changes=['public numerical leaf guard', 'fixed c=0 hypothesis',
                         'equivalent malformed-input rejection',
                         'named checker with uniformly null successful return'])

def run(checker, payload, optimized):
    cmd = [sys.executable, '-I', '-S', '-B']
    if optimized:
        cmd.append('-O')
    cmd.append(str(ROOT / checker))
    process = subprocess.run(cmd, input=payload, capture_output=True, timeout=30)
    return process.returncode == 0 and process.stdout == b'ACCEPT\n'

def alias_goal(value):
    # This operation changes the public formula ONLY in negative controls.
    # It is never used to compile a positive proof certificate.
    if type(value) is list:
        return [alias_goal(x) for x in value]
    return 1 if value == 0 else value

def main():
    audit = structural_audit()
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    for entry in provenance['reference_files']:
        raw = (ROOT / entry['local_path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if blob != entry['expected_git_blob_sha']:
            raise AssertionError('Changed reference blob: ' + entry['local_path'])
    candidates = ['alias_inverted.py', 'checker_readable.py']
    metrics = [metric(ROOT / f) for f in candidates + [
        'ref/immediate_application/code/checker637.py',
        'ref/verified_refinements/strict/checker.py',
        'ref/immediate_application/code/checker479.py']]
    if tuple(metrics[0][k] for k in ('tokens', 'ast_nodes', 'normalized_bytes')) != (331, 373, 625):
        raise AssertionError(metrics[0])
    fixtures = []
    def add(name, value, expected, group):
        fixtures.append(dict(name=name, payload=(json.dumps(value, separators=(',', ':'))+'\n').encode(),
                             expected=expected, group=group))
    generated = json.loads((ROOT / 'generated_cases.json').read_text())
    for case in generated:
        value = json.loads((ROOT / case['file']).read_text())
        add(case['name'], value, True, 'compiled_positive')
        false_goal = copy.deepcopy(value)
        false_goal[-1] = [1, [1]]
        add(case['name'] + '_false_goal', false_goal, False, 'false_conclusion')
        # A particular instruction may be redundant.  Removing the whole
        # certificate is the unambiguous missing-proof negative control.
        add(case['name'] + '_missing_certificate', [value[-1]], False, 'missing_premise')
    base = json.loads((ROOT / generated[-1]['file']).read_text())
    for j, bad in enumerate([None, True, False, 0.0, 1.0, {}, '0', [[None]]]):
        add('unused_invalid_prefix_' + str(j), [bad] + base, False, 'whole_input_types')
    for j, good in enumerate([0, [], [1, 0], [-999], [[[2]]]]):
        add('unused_valid_prefix_' + str(j), [good] + base, True, 'whole_input_types')
    for j, bad in enumerate([0, [], [0, 0], [1], [1, 2], [3, 3], [-1, -1], [1,1,1,1]]):
        add('invalid_public_root_' + str(j), base[:-1] + [bad], False, 'public_grammar')
    # An actual generated binder proof with an unallocated supplied witness.
    for case in generated:
        if case['name'] != 'nonvacuous_witness':
            continue
        value = json.loads((ROOT / case['file']).read_text())
        for index, packet in enumerate(value[:-1]):
            if packet[:2] == [0, 0] and packet[2] in (0, []):
                attack = copy.deepcopy(value)
                attack[index][3] = -999
                add(case['name'] + '_future_witness', attack, False, 'scope')
                break
    # Reuse the inherited adversarial certificates, changing only their
    # public equation to the new syntax. These are negative controls.
    inherited = ROOT / 'ref/immediate_application/tests/native/proofs'
    for case in json.loads((inherited / 'cases.json').read_text()):
        if case['expected']:
            continue
        value = json.loads((inherited / case['file']).read_text())
        value[-1] = alias_goal(value[-1])
        add('inherited_' + case['file'], value, False, 'inherited_negative')
    newdir = ROOT / 'fixtures' / 'checks'
    newdir.mkdir(parents=True, exist_ok=True)
    for previous in newdir.glob('*.json'):
        previous.unlink()
    for fixture in fixtures:
        (newdir / (fixture['name'] + '.json')).write_bytes(fixture['payload'])
    tasks = [(f, c, o) for f in fixtures for c in candidates for o in (False, True)]
    def execute(task):
        f, c, o = task
        accepted = run(c, f['payload'], o)
        return dict(group=f['group'], fixture=f['name'], checker=c,
                    optimized=o, accepted=accepted, expected=f['expected'],
                    passed=accepted == f['expected'],
                    input_sha256=hashlib.sha256(f['payload']).hexdigest())
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(execute, tasks))
    # Confirm the current upstream controls reproduce all 121 inherited
    # expectations in their OWN unchanged interfaces.
    upstream_results = []
    for folder in (ROOT / 'ref/immediate_application/tests').rglob('cases.json'):
        checker = ('ref/immediate_application/code/checker637.py' if
                   '/native/' in str(folder) else
                   'ref/immediate_application/code/checker479.py')
        for case in json.loads(folder.read_text()):
            payload = (folder.parent / case['file']).read_bytes()
            for optimized in (False, True):
                accepted = run(checker, payload, optimized)
                upstream_results.append(dict(file=str((folder.parent / case['file']).relative_to(ROOT)),
                    checker=checker, optimized=optimized, accepted=accepted,
                    expected=case['expected'], passed=accepted == case['expected']))
    # The c=0 resource is necessary for the translated zero computation.
    noalias = (ROOT / 'alias_inverted.py').read_text().replace(
        'c([0, [1, 0]], q(), v=1)', 'c([0], q(), v=1)')
    controls = ROOT / 'negative_controls'
    controls.mkdir(exist_ok=True)
    (controls / 'without_alias.py').write_text(noalias)
    witness = next(x for x in fixtures if x['name'] == 'zero_computation')
    noalias_results = [dict(optimized=o,
                           accepted=run('negative_controls/without_alias.py', witness['payload'], o))
                       for o in (False, True)]
    if any(x['accepted'] for x in noalias_results):
        raise AssertionError('Alias axiom negative control unexpectedly accepted')
    report = dict(python=platform.python_version(), scope='Canonical public encodings; arity grammar and entire input alphabet checked',
                  structural_audit=audit, metrics=metrics,
                  candidate_distinct_cases=len(fixtures), candidate_executions=len(results),
                  candidate_failures=sum(not x['passed'] for x in results),
                  upstream_distinct_cases=len(upstream_results)//2,
                  upstream_executions=len(upstream_results),
                  upstream_failures=sum(not x['passed'] for x in upstream_results),
                  without_alias_control=noalias_results,
                  reference_blob_verification=dict(files=len(provenance['reference_files']), all_matched=True),
                  candidate_checks=results, upstream_checks=upstream_results)
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('candidate_checks','upstream_checks')}, indent=2))
    if report['candidate_failures'] or report['upstream_failures']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
