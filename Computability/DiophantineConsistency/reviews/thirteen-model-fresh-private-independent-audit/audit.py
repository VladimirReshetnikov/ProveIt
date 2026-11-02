#!/usr/bin/env python3
"""Read-only independent check of the conditional two-parent suffix replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
PKG = BASE / 'research/thirteen-model-fresh-private'
OUT = Path('/tmp/ipra-thirteen-fresh-private-pair-01')
AUX = Path('/tmp/ipra-thirteen-aux-seed-pair-01')
NEG = Path('/tmp/ipra-thirteen-negative-residue-pair-01')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT = '08fba9296d09639e614ce5716a4e02b35ee4235134a9e63234fd719762db3958'
NAMES = ('ModelBPositiveCarrier', 'ModelBFreshPrivate')
OBJS = ('9d91b29718664bb7731cf3660fc27216e68d5ee4a3f971090112c573696be8ed',
        '3e6d8214a4de509e3a8dff0fbe7b457dbb4ed1eb0e3141c5124e0181067b5e2f')
NEG_NAMES = ('DiscreteOrderedRingFacts', 'ArithmeticNegativeNorms', 'ModelArithmetic',
             'ArithmeticOddOrdinateResidue', 'ModelBNegativeResidue')

def need(test, label):
    if not test:
        raise ValueError(label)

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for name in ('README.md', 'replay.py', 'replay-receipt.json', 'terminal-observation.json', *(x + '.lean' for x in NAMES)):
        p = PKG / name
        blob = subprocess.run(['git', 'show', '6e71b6c877:' + p.relative_to(ROOT).as_posix()],
                              cwd=ROOT, check=True, stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest() == sha(p), 'committed bytes ' + name)
    obs = json.loads((PKG / 'terminal-observation.json').read_bytes())
    need(obs == {'outer_exit_code': 0, 'output': str(OUT), 'receipt_sha256': RECEIPT,
                 'session_id': 72170, 'stdout': 'PASS_PAIRED_THIRTEEN_FRESH_PRIVATE ' + RECEIPT}, 'outer observation')
    need(sha(PKG / 'replay-receipt.json') == sha(OUT / 'receipt.json') == RECEIPT, 'receipt bytes')
    r = json.loads((PKG / 'replay-receipt.json').read_bytes())
    need(r['status'] == 'PASS_PAIRED_THIRTEEN_FRESH_PRIVATE' and len(r['runs']) == 2, 'status')
    for p, h in r['fixed_inputs_sha256'].items():
        need(sha(p) == h, 'fixed input ' + p)
    for sub, h in [('thirteen-model-auxiliary-seed-independent-audit', '795223c9125a4df837af0390dbd557024d63658e665474dae282d21c88f9308d'),
                   ('thirteen-model-negative-residue-independent-audit', '9811fa9f3254c35268accfba801002856880fe208eb75c991a76bc97cd8447a5')]:
        d = BASE / 'reviews' / sub
        need(sha(d / 'CHECK.json') == h, 'parent receipt pin')
        p = subprocess.run([sys.executable, '-I', '-S', '-B', str(d / 'audit.py')], capture_output=True, timeout=180)
        need(p.returncode == 0 and not p.stderr and json.loads(p.stdout) == json.loads((d / 'CHECK.json').read_bytes()), 'parent re-audit ' + sub)
    summaries = []
    for row, side in zip(r['runs'], ('author', 'peer')):
        run = OUT / side
        project = run / 'lib/DiophantineConsistency'
        aux = AUX / side / 'lib/DiophantineConsistency'
        neg = NEG / side / 'lib/DiophantineConsistency'
        need(row['label'] == side and len(row['modules']) == 2, 'side modules')
        links = row['parent_links']
        need(len(links) == 74 and len(list(aux.glob('*.olean'))) == 69, 'parent counts')
        expected = {str(project / p.name): p for p in aux.glob('*.olean')}
        for name in NEG_NAMES:
            target = neg / (name + '.olean')
            key = str(project / target.name)
            need(key not in expected, 'parent collision')
            expected[key] = target
        need(set(links) == set(expected), 'parent link coverage')
        for path, target in expected.items():
            p = Path(path)
            need(p.is_symlink() and p.resolve() == target.resolve() and
                 links[path]['target'] == str(target) and sha(p) == links[path]['sha256'], 'link ' + path)
        bb = run / 'lib/BusyBeaver'
        need(bb.is_symlink() and bb.resolve() == (AUX / side / 'lib/BusyBeaver').resolve(), 'BusyBeaver link')
        for i, (item, name) in enumerate(zip(row['modules'], NAMES)):
            src = run / 'src/DiophantineConsistency' / (name + '.lean')
            obj = project / (name + '.olean')
            need(item['name'] == name and item['exit'] == item['deps_exit'] == 0 and not item['stderr'], 'child exits')
            need(sha(src) == sha(PKG / (name + '.lean')) == item['source_sha256'], 'compiled source')
            need(not obj.is_symlink() and sha(obj) == item['object_sha256'] == OBJS[i], 'compiled object')
            need(item['command'][1:4] == ['-M4000', '-j1', '-DElab.async=false'] and
                 item['command'][-1] == str(obj), 'bounded command')
            imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', src.read_text(), re.M)
            deps = {str(PACKAGE / 'Init.olean')}
            for dep in imports:
                path = run / 'lib' / Path(*dep.split('.')).with_suffix('.olean')
                need(path.is_file(), 'import exists')
                deps.add(str(path))
            need(set(item['deps_stdout'].splitlines()) == deps, 'recorded direct imports')
            warnings = [x.split('warning:', 1)[1].strip() for x in item['stdout'].splitlines() if 'warning:' in x]
            need(len(warnings) == (3 if i == 0 else 0) and all(x.startswith('`push_neg` has been deprecated.') for x in warnings), 'warnings')
            need(not re.search(r'\b(?:sorryAx|sorry|admit|admitted)\b|^.*error:', item['stdout'], re.M), 'admission or error')
            need(item['axiom_reports'] == ['propext, Classical.choice, Quot.sound'] and
                 re.search(r"depends on axioms: \[propext, Classical.choice, Quot.sound\]", item['stdout']), 'axioms')
        summaries.append({'side': side, 'parent_links': len(links), 'recorded_compiler_exits': [0, 0],
                          'recorded_dependency_exits': [0, 0], 'objects': list(OBJS), 'carrier_warnings': 3})
    print(json.dumps({'status': 'PASS_INDEPENDENT_THIRTEEN_FRESH_PRIVATE_AUDIT', 'source_commit': '6e71b6c877',
      'author_receipt_sha256': RECEIPT, 'recorded_outer_session': 72170, 'recorded_outer_exit': 0,
      'parent_audits_rerun_exit': [0, 0], 'runs': summaries,
      'scope': 'Read-only audit of paired model suffix over two audited parents; no Lean rerun, graph converse, fixed-port calibration, or object-theory iPRA proof.'}, indent=2))

if __name__ == '__main__':
    main()
