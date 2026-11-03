#!/usr/bin/env python3
"""Read-only independent check of seed digits, receipts, and refusal guards."""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
P = D / 'research/current14-seed-lines-binding'
seed_file = D / 'Lean/DiophantineConsistency/DecimalMachine215.lean'
tex = D / 'equation.tex'
pdf = D / 'equation.pdf'

def must(ok, message):
    if not ok:
        raise SystemExit(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

pins = {
    'SeedLines.lean': '36bd157407732377d364186378980650c48c89b6dfee63d5688234791e7ff8d3',
    'SeedLines-string-attempt.txt': '42ed41bdced06611f91ae69b19ce26397b90e58f75ed7e605872b3965a7ca9b6',
    'observation.json': 'f455b429d08f18abfab61b54716b1c5ca70231511374d323272dd750dcd93603',
    'attempt01.json': '7bc436a8d3f6b4d691027f59a77c1eb5084dca8110113c86bcd09d0750c6692f',
    'display-observation.json': '5f0425f6f64bba649b80d4f49543b87400ad60ee8b522f2f2b63fc3bb5ba25fa',
    'refusal-observation.json': 'ac3756d141c4ad56862404f8d22d52e0050dfcb438b0e3e9a66eb84489a6febf',
    'run.py': 'ff33cce08d2eccf5459fb045f644548b8aa50079498ce69341e2911ba910de03',
    'run-captured.txt': '7ec65afb1b0b3e22fdf64cb3ab0161b60d4855292f965282193c2b80154fa19a',
    'check_display.py': 'f82181416fe951875173342023265b94261c514c4b79301d7abc5876a14d7a57',
    'observations/second-author/observation.json': '80e6a594d220d8249f7c11b469b7f4d16c777a25cf8d5d6ad8013659ddf0fab2',
}
for name, expected in pins.items():
    must(sha(P / name) == expected, 'author-file hash mismatch: ' + name)

source = (P / 'SeedLines.lean').read_text()
marker = 'def lines : List (List ℕ) := '
must(source.count(marker) == 1, 'ambiguous digit list definition')
list_text = source.split(marker, 1)[1].split('\n]\n', 1)[0] + '\n]'
lines = ast.literal_eval(list_text)
must(isinstance(lines, list) and len(lines) == 12, 'invalid line count')
must([len(line) for line in lines] == [62] * 11 + [33], 'line lengths differ')
must(all(type(d) is int and 0 <= d < 10 for line in lines for d in line), 'invalid digit')
line_strings = [''.join(map(str, line)) for line in lines]
must([i + 1 for i, line in enumerate(line_strings) if line.startswith('0')] == [7], 'leading zero line changed')
joined = ''.join(line_strings)
folded = 0
for line in lines:
    for digit in line:
        folded = 10 * folded + digit
must(len(joined) == 715 and folded == int(joined), 'decimal fold mismatch')
seed_lines = [line for line in seed_file.read_text().splitlines() if line.startswith('def seed : ℕ := ')]
must(len(seed_lines) == 1, 'ambiguous seed source')
seed_string = seed_lines[0].split(' := ', 1)[1]
must(seed_string.isascii() and seed_string.isdecimal() and int(seed_string) == folded, 'seed source numeral mismatch')
tex_rows = [line[:-4] for line in tex.read_text().splitlines() if line.endswith('\\par') and line[:-4].isascii() and line[:-4].isdecimal()]
must(tex_rows == line_strings, 'TeX digit rows mismatch')
pdf_read = subprocess.run(['pdftotext', '-raw', str(pdf), '-'], capture_output=True, check=True)
must(not pdf_read.stderr, 'pdftotext stderr')
pdf_rows = [line.strip() for line in pdf_read.stdout.decode().splitlines() if len(line.strip()) in (33, 62) and line.strip().isascii() and line.strip().isdecimal()]
must(pdf_rows == line_strings, 'PDF-extracted digit rows mismatch')

saved_display = json.loads((P / 'display-observation.json').read_text())
for rel, digest in saved_display['inputs_sha256'].items():
    must(sha(D / rel) == digest, 'display input hash mismatch: ' + rel)
must(hashlib.sha256(pdf_read.stdout).hexdigest() == saved_display['pdf_extraction_sha256'], 'PDF extraction hash mismatch')
checker = subprocess.run([sys.executable, '-I', '-S', '-B', str(P / 'check_display.py')], capture_output=True, check=True)
must(not checker.stderr and json.loads(checker.stdout) == saved_display, 'author checker output mismatch')
optimized = subprocess.run([sys.executable, '-I', '-S', '-B', '-O', str(P / 'check_display.py')], capture_output=True, text=True)
must(optimized.returncode != 0 and 'Optimized Python is not accepted' in optimized.stderr, 'display optimized guard failed')

first = json.loads((P / 'observation.json').read_text())
second = json.loads((P / 'observations/second-author/observation.json').read_text())
failed = json.loads((P / 'attempt01.json').read_text())
expected_axiom = "'DiophantineConsistency.Current14SeedLines.decimal_lines_eq_seed' does not depend on any axioms\n"
direct = Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib/DiophantineConsistency/DecimalMachine215.olean')
object_digest = '167d2a0d1301346f696657e2ee44d35dec4b103c8e48adfec0eb78175eba8d9c'
for index, receipt in enumerate((first, second), 1):
    must(receipt['exit'] == 0 and receipt['reason'] is None and receipt['before'] == receipt['after'], 'successful receipt failed')
    must(receipt['stdout'] == expected_axiom and receipt['stderr'] == '', 'axiom/stderr report mismatch')
    must(receipt['object_sha256'] == object_digest, 'object receipt mismatch')
    must(receipt['before'][str(direct)]['sha256'] == sha(direct), 'direct imported object hash mismatch')
    must(receipt['before'][str(direct)]['realpath'] == str(direct.resolve()), 'direct imported object resolution mismatch')
    must(receipt['before'][str(P / 'SeedLines.lean')]['sha256'] == sha(P / 'SeedLines.lean'), 'theorem source hash mismatch')
    lean = Path(receipt['command'][0])
    must(receipt['before'][str(lean)]['sha256'] == sha(lean), 'Lean binary hash mismatch')
    must(receipt['before'][str(lean)]['realpath'] == str(lean.resolve()), 'Lean binary resolution mismatch')
    runner_path = P / ('run-captured.txt' if index == 1 else 'run.py')
    must(receipt['before'][str(P / 'run.py')]['sha256'] == sha(runner_path), 'runner bytes mismatch')
    must(receipt['command'][-1] == str(P / 'SeedLines.lean'), 'Lean source argument mismatch')
    must(receipt['lean_path'].split(':')[0] == str(direct.parents[1]), 'unexpected first provider')
    out = Path(receipt['command'][receipt['command'].index('-o') + 1])
    must(sha(out) == object_digest, 'produced Lean object mismatch')
    if index == 2:
        must((out.parent / 'stdout.log').read_text() == receipt['stdout'], 'second output log mismatch')
        must((out.parent / 'stderr.log').read_text() == receipt['stderr'], 'second error log mismatch')
    must(receipt['preflight']['available_kib'] >= 8*1024*1024 and len(receipt['preflight']['lean_processes']) < 2, 'bad preflight guard')
    must(all(s['available_kib'] >= 8*1024*1024 and len(s['lean_processes']) <= 2 for s in receipt['samples']), 'bad sampled guard')
must(failed['exit'] != 0 and failed['object_sha256'] is None and 'sorryAx' in failed['stdout'], 'earlier failure receipt mismatch')
must(failed['before'][str(P / 'SeedLines.lean')]['sha256'] == sha(P / 'SeedLines-string-attempt.txt'), 'failed attempt source mismatch')
refusal = json.loads((P / 'refusal-observation.json').read_text())
must(refusal['before'] == refusal['after'] and refusal['object_hashes_match'], 'saved refusal guard mismatch')
protected = [P / 'observation.json', P / 'attempt01.json', P / 'observations/second-author/observation.json',
             Path(first['command'][first['command'].index('-o')+1]), Path(second['command'][second['command'].index('-o')+1])]
before = [sha(path) for path in protected]
for flags, expected in [([], 'Attempt already exists'), (['-O'], 'Optimized Python is not accepted')]:
    result = subprocess.run([sys.executable, '-I', '-S', '-B', *flags, str(P / 'run.py'), '--attempt', 'second-author'], capture_output=True, text=True)
    must(result.returncode != 0 and expected in result.stderr and not result.stdout, 'runner refusal failed')
must(before == [sha(path) for path in protected], 'runner refusals changed a protected output')
for name, expected in pins.items():
    must(sha(P / name) == expected, 'author file changed during review: ' + name)
for rel, expected in saved_display['inputs_sha256'].items():
    must(sha(D / rel) == expected, 'display input changed during review: ' + rel)
must(sha(direct) == first['before'][str(direct)]['sha256'], 'direct object changed during review')
print(json.dumps({'digits': len(joined), 'line_lengths': [len(row) for row in line_strings],
                  'leading_zero_lines': [7], 'source_and_pdf_match': True,
                  'author_display_rerun': 'PASS', 'two_success_receipts': 'PASS',
                  'same_output_hash': object_digest, 'direct_import_sha256': sha(direct),
                  'runner_refusals_unchanged': True}, indent=2))
