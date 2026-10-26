from pathlib import Path
import argparse
import difflib
import hashlib
import json

parser = argparse.ArgumentParser()
parser.add_argument('--repo', required=True, type=Path)
args = parser.parse_args()
HERE = Path(__file__).resolve().parent
REPO = args.repo.resolve()
PREFIX = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
HELPER = HERE / 'lean/DiophantineConsistency/ArithmeticCertificates.lean'
patches = []
metrics = []

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

for name in ('RegisterDivMod', 'QuadraticDivMod'):
    relative = PREFIX / (name + '.lean')
    before = (REPO / relative).read_text()
    start = before.index('theorem certificate_iff (q r n b : ℕ) :')
    stop = before.index('\n\n/-- Source inputs', start)
    declaration = before[start:stop]
    statement = declaration.split(' := by', 1)[0]
    replacement = statement + ' :=\n  ArithmeticCertificates.divMod_certificate_iff q r n b'
    after_without_import = before[:start] + replacement + before[stop:]
    after = 'import DiophantineConsistency.ArithmeticCertificates\n' + after_without_import
    (HERE / 'patched-modules' / relative.name).write_text(after)
    patches.append(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile='a/' + str(relative), tofile='b/' + str(relative))))
    before_rest = before[:start] + before[stop:]
    after_start = after_without_import.index('theorem certificate_iff (q r n b : ℕ) :')
    after_stop = after_without_import.index('\n\n/-- Source inputs', after_start)
    after_rest = after_without_import[:after_start] + after_without_import[after_stop:]
    assert before_rest == after_rest
    assert statement == replacement.split(' :=', 1)[0]
    metrics.append(dict(path=str(relative), original_lines=len(before.splitlines()),
        candidate_lines=len(after.splitlines()), old_declaration_lines=len(declaration.splitlines()),
        new_declaration_lines=len(replacement.splitlines()),
        statement_sha256=digest(statement), unchanged_remainder_sha256=digest(before_rest),
        unchanged_remainder_verified=True))

helper_text = HELPER.read_text()
patches.append(''.join(difflib.unified_diff([], helper_text.splitlines(True),
    fromfile='/dev/null', tofile='b/' + str(PREFIX / HELPER.name))))
(HERE / 'patches/arithmetic-certificates.patch').write_text(''.join(patches))
result = dict(base_commit='6175dff9a15491497c7a3c1bda4f6a62a6349c74',
    modules=metrics, helper_lines=len(helper_text.splitlines()),
    old_total_lines=sum(x['original_lines'] for x in metrics),
    candidate_total_lines=sum(x['candidate_lines'] for x in metrics) + len(helper_text.splitlines()),
    optional_checks_excluded_from_production_delta=True,
    note='Full module rest equality excludes only the replaced theorem declaration and one new import.')
result['net_lines_saved'] = result['old_total_lines'] - result['candidate_total_lines']
(HERE / 'evidence/source-metrics.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
