#!/usr/bin/env python3
"""Audit both completed 104-stage ledgers and all retained peer comparisons.

No Lean is invoked. Byte-level differences and inherited ancestry are not
treated as proved semantic equivalences.
"""
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
REVIEWS = HERE.parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
RUNNER = DC / 'research/nine-variable-ipra/bounded-build-preflight/replay.py'
AUTHOR = Path('/tmp/nine-ipra-guarded-author-20261102-h')
PEER = Path('/tmp/nine-ipra-guarded-peer-20261102-a')
PACKETS = [
    ('nine-variable-ipra-peer-first-five', 1, 5),
    ('nine-variable-ipra-peer-stages-six-ten', 6, 10),
    ('nine-variable-ipra-peer-stages-eleven-fifteen', 11, 15),
    ('nine-variable-ipra-peer-stages-sixteen-twenty', 16, 20),
    ('nine-variable-ipra-peer-stages-twentyone-twentyfive', 21, 25),
    ('nine-variable-ipra-peer-stages-26-30', 26, 30),
    ('nine-variable-ipra-peer-stages-31-35', 31, 35),
    ('nine-variable-ipra-peer-stages-36-40', 36, 40),
    ('nine-variable-ipra-peer-stages-41-45', 41, 45),
    ('nine-variable-ipra-peer-stages-46-50', 46, 50),
    ('nine-variable-ipra-peer-stages-51-55', 51, 55),
    ('nine-variable-ipra-peer-stages-56-60', 56, 60),
    ('nine-variable-ipra-peer-stages-61-65', 61, 65),
    ('nine-variable-ipra-peer-stages-66-70', 66, 70),
    ('nine-variable-ipra-peer-stages-71-75', 71, 75),
    ('nine-variable-ipra-peer-stages-76-80', 76, 80),
    ('nine-variable-ipra-peer-stage-81', 81, 81),
    ('nine-variable-ipra-peer-stages-82-86', 82, 86),
    ('nine-variable-ipra-peer-stages-87-91', 87, 91),
    ('nine-variable-ipra-peer-stages-92-96', 92, 96),
    ('nine-variable-ipra-peer-stages-97-101', 97, 101),
    ('nine-variable-ipra-peer-stages-102-104', 102, 104),
]


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def run_ledger(name, root):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                          '--output', str(root), '--check'], cwd=ROOT,
                         capture_output=True, text=True, timeout=180)
    need(run.returncode == 0 and not run.stderr and run.stdout.strip() == 'ALL_STAGES_RECORDED 104',
         (name, run.returncode, run.stdout, run.stderr))


def named_axioms(log, source, namespace=None):
    reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S)
    declared = re.findall(r'^#print axioms (\S+)', source, re.M)
    actual = [name if namespace is None else name.rsplit('.', 1)[-1] for name, _ in reports]
    need(actual == declared and len(reports) == (15 if namespace is None else 4) and
         all({x.strip() for x in axioms.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
             for _, axioms in reports), ('named axiom reports mismatch', namespace))
    return [name for name, _ in reports]


for name, root in [('author', AUTHOR), ('peer', PEER)]:
    run_ledger(name, root)
ma, mb = [json.loads((root / 'manifest.json').read_text()) for root in (AUTHOR, PEER)]
need(ma['modules'] == mb['modules'] and len(ma['modules']) == 104 and
     ma['runner_sha256'] == mb['runner_sha256'] == digest(RUNNER), 'plan/runner mismatch')

packet_rows = []
stage_packets = {}
for name, lo, hi in PACKETS:
    packet = REVIEWS / name; obs = packet / 'observations'
    terminal = json.loads((obs / 'terminal.json').read_text())
    first = name.endswith('first-five')
    audit = packet / ('compare.py' if first else 'audit.py')
    stdout = obs / ('compare.stdout' if first else 'audit.stdout')
    stderr = obs / ('compare.stderr' if first else 'audit.stderr')
    key = 'compare_sha256' if first else 'audit_sha256'
    need(terminal['exit_code'] == 0 and terminal[key] == digest(audit) and
         terminal['capture_sha256'] == digest(packet / 'capture.py') and
         terminal['stdout_sha256'] == digest(stdout) and terminal['stderr_sha256'] == digest(stderr) and
         not stderr.read_bytes(), ('packet terminal mismatch', name))
    output = json.loads(stdout.read_text()); stages = [r['stage'] for r in output['stages']]
    need(stages == list(range(lo, hi+1)), ('packet stage coverage mismatch', name, stages))
    for i in stages:
        need(i not in stage_packets, ('overlapping packet stages', i))
        stage_packets[i] = (name, output['stages'][i-lo])
    packet_rows.append({'path': str(packet.relative_to(ROOT)), 'first_stage': lo, 'last_stage': hi,
                        'status': output['status'], 'audit_sha256': digest(audit),
                        'terminal_sha256': digest(obs / 'terminal.json'),
                        'stdout_sha256': digest(stdout), 'readme_sha256': digest(packet / 'README.md')})
need(sorted(stage_packets) == list(range(1, 105)), 'stage packets incomplete')

rows = []; object_differences = []; direct_differences = []; named_reports = {}
for i in range(1, 105):
    paths = [root / 'receipts' / f'{i:03d}.json' for root in (AUTHOR, PEER)]
    a, b = [json.loads(p.read_text()) for p in paths]
    name, summary = stage_packets[i]; packet = REVIEWS / name
    need(a['status'] == b['status'] == 'PASS' and a['module'] == b['module'] == ma['modules'][i-1]['module']
         and a['source_sha256'] == b['source_sha256'] and summary['module'] == a['module'] and
         summary['source_sha256'] == a['source_sha256'], ('stage source/status mismatch', i))
    need(summary['author_receipt_sha256'] == digest(paths[0]) and
         summary['peer_receipt_sha256'] == digest(paths[1]), ('packet receipt pin mismatch', i))
    if 'object_sha256' in summary:
        need(summary['object_sha256'] == a['output']['sha256'] == b['output']['sha256'],
             ('packet object pin mismatch', i))
    else:
        need(summary['author_object_sha256'] == a['output']['sha256'] and
             summary['peer_object_sha256'] == b['output']['sha256'], ('packet object pin mismatch', i))
    for label, root, receipt, path in [('author', AUTHOR, a, paths[0]), ('peer', PEER, b, paths[1])]:
        saved = packet / 'observations' / label / f'{i:03d}'
        # Scoped-match packets and discrepancy packets use the same retained layout.
        need((saved / 'receipt.json').read_bytes() == path.read_bytes(), ('captured receipt drift', i, label))
        stage_source = Path(receipt['command'][5]); saved_source = saved / stage_source.name
        need(digest(stage_source) == digest(saved_source) == receipt['source_sha256'], ('captured source drift', i, label))
        log = Path(receipt['log']); need(digest(log) == digest(saved / 'compile.log') == receipt['log_sha256'],
                                         ('captured log drift', i, label))
        for fname in ('deps.stdout', 'deps.stderr'):
            need((saved / fname).read_bytes() == (log.parent / fname).read_bytes(),
                 ('captured dependency output drift', i, label, fname))
        need(digest(Path(receipt['output']['resolved'])) == receipt['output']['sha256'],
             ('output drift', i, label))
    logs = [Path(r['log']).read_text().replace(r['command'][5], '<SOURCE>') for r in (a, b)]
    need(logs[0] == logs[1], ('normalized log mismatch', i))
    inputs = [{module: info['record']['sha256'] for module, info in r['direct'].items()} for r in (a, b)]
    differences = [{'module': k, 'author_sha256': inputs[0].get(k), 'peer_sha256': inputs[1].get(k)}
                   for k in sorted(inputs[0].keys() | inputs[1].keys())
                   if inputs[0].get(k) != inputs[1].get(k)]
    object_equal = a['output']['sha256'] == b['output']['sha256']
    entry = {'stage': i, 'module': a['module'], 'packet': name, 'source_sha256': a['source_sha256'],
             'author_output_sha256': a['output']['sha256'], 'peer_output_sha256': b['output']['sha256'],
             'output_equal': object_equal, 'direct_input_differences': differences,
             'normalized_log_sha256': sha256(logs[0].encode()).hexdigest(),
             'author_receipt_sha256': digest(paths[0]), 'peer_receipt_sha256': digest(paths[1])}
    if not object_equal:
        object_differences.append(entry)
    if differences:
        direct_differences.append({'stage': i, 'module': a['module'], 'differences': differences})
    if i in (81, 104):
        named_reports[str(i)] = named_axioms(logs[0], Path(a['command'][5]).read_text(),
                                              None if i == 81 else 'IPRAExplicitZFCFinal')
    rows.append(entry)

need(ma['modules'][79]['module'] == 'DiophantineConsistency.IPRANineCurrent' and
     ma['modules'][80]['module'] == 'DiophantineConsistency.IPRANineChecks' and
     ma['modules'][103]['module'] == 'DiophantineConsistency.IPRAExplicitZFCFinal', 'endpoint order')
for i in (80, 104):
    source = Path(json.loads((AUTHOR / 'receipts' / f'{i:03d}.json').read_text())['command'][5]).read_text()
    for suffix in ('native_equivalence', 'standard_equivalence', 'reference_equivalence'):
        need(re.search(r'\btheorem\s+' + suffix + r'\s*:', source) is not None,
             ('endpoint source declaration absent', i, suffix))
    need('⊢' in source and 'mappedNativeRefutation embedding' in source, ('endpoint syntax missing', i))
    text = ' '.join(source.split())
    expression = 'expression' if i == 80 else 'ExplicitZFCSyntax.expression'
    for theory, suffix in [('nativeTheory', 'native_equivalence'),
                           ('IPRAStandardTheory.standardTheory', 'standard_equivalence')]:
        statement = (f'theorem {suffix} : {theory} ⊢ '
                     f'IPRAExpressionNative.nativeNoZero {expression} 🡘 '
                     '∼mappedNativeRefutation embedding :=')
        need(statement in text, ('unexpected endpoint statement', i, suffix))
    reference = ('theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢ '
                 f'IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero {expression}) 🡘 '
                 '∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=')
    need(reference in text, ('unexpected reference endpoint statement', i))
need(rows[79]['output_equal'] and rows[80]['output_equal'] and rows[103]['output_equal'],
     'endpoint/check output differs')
need(len(object_differences) == 20 and len(direct_differences) == 28, 'discrepancy counts changed')
print(json.dumps({'status': 'BOTH_104_STAGE_LEDGERS_RECORDED_IMPORT_DIFFERENCES_REMAIN',
                  'runner_sha256': digest(RUNNER), 'author_manifest_sha256': digest(AUTHOR / 'manifest.json'),
                  'peer_manifest_sha256': digest(PEER / 'manifest.json'),
                  'packets': packet_rows, 'stages': rows, 'output_object_differences': object_differences,
                  'stages_with_different_direct_input_hashes': direct_differences,
                  'named_axiom_reports': named_reports,
                  'scope': 'recorded 104-stage author/peer ledgers and retained comparisons, no new Lean; '
                           'raw object/import differences, inherited transitive project/package/dynamic '
                           'ancestry and document/PDF binding remain open'}, indent=2, sort_keys=True))
