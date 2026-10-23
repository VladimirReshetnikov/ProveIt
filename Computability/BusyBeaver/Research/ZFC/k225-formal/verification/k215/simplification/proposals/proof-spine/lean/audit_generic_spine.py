#!/usr/bin/env python3
"""Read-only static audit owned by this proposal, not a Lean verifier.

Inputs are pinned repository text and a proposed overlay. No imported or
received source is executed. Run from any directory with Python 3.10+.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re
import sys

if not __debug__:
    raise SystemExit('Refuse Python -O: static checks must remain enabled.')

HERE = Path(__file__).resolve().parent
RAW_REVIEW = HERE.parent / 'review'
REVIEW = RAW_REVIEW
if not (REVIEW / 'source_manifest.json').exists():
    REVIEW = REVIEW / 'deliverable'
PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
PREFIX = 'BusyBeaver.ZFC.'
REPO = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
NS = 'SetTheory.BusyBeaver.ZFC.'

def need(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)

def imports(content):
    return re.findall(r'^import ([A-Za-z0-9_.]+)\s*$', content, re.M)

def metrics(source):
    return {'modules': len(source),
            'bytes': sum(len(t.encode()) for t in source.values()),
            'lines': sum(len(t.splitlines()) for t in source.values())}

snapshot = json.loads((REVIEW / 'source_manifest.json').read_text())['snapshots']['current']
need(snapshot['pin'] == PIN, 'wrong baseline pin')
records = {r['module']: r for r in snapshot['rows']}
need(len(records) == 174, 'unexpected endpoint baseline count')
compatibility = json.loads((HERE / 'compatibility_source_manifest.json').read_text())
need(compatibility['pin'] == PIN, 'wrong compatibility pin')
full_ledger_path = next((p for p in [REVIEW / 'current_source_ledger.json',
    RAW_REVIEW / 'current_source_ledger.json'] if p.exists()), None)
if full_ledger_path is not None:
    full_ledger = json.loads(full_ledger_path.read_text())
    need(full_ledger['pin'] == PIN, 'wrong full-ledger pin')
    records = full_ledger['sources']
    need(len(records) == 203, 'unexpected full source count')
else:
    records.update(compatibility['sources'])
baseline = {}
for module, record in records.items():
    source_path = REVIEW / 'snapshots' / 'current' / record['path']
    if not source_path.exists() and full_ledger_path is not None:
        source_path = REVIEW / 'snapshots' / 'compatibility' / record['path']
    if not source_path.exists() and full_ledger_path is not None:
        source_path = RAW_REVIEW / 'current' / record['path']
    if full_ledger_path is None and module in compatibility['sources']:
        source_path = HERE / 'current' / Path(record['path']).name
    raw = source_path.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == record['sha256'], 'SHA-256: ' + module)
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    need(blob == record['git_blob_sha'], 'Git blob: ' + module)
    text = raw.decode()
    need(imports(text) == record['imports'], 'imports differ: ' + module)
    baseline[module] = text
need(len(baseline) == (203 if full_ledger_path is not None else 175),
     'unexpected baseline source count')

candidate_root = HERE / 'candidate'
overlay = {'.'.join(p.relative_to(candidate_root).with_suffix('').parts): p.read_text()
           for p in candidate_root.rglob('*.lean')}
need(len(overlay) == 12, 'unexpected candidate file count')

def closure(source):
    seen = {}
    visiting = set()
    def visit(module):
        if module == 'Init':
            return  # Lean's implicit standard module is outside project census.
        need(module not in visiting, 'cyclic import: ' + module)
        if module in seen:
            return
        need(module in source, 'unresolved project import: ' + module)
        visiting.add(module)
        for dep in imports(source[module]):
            visit(dep)
        visiting.remove(module)
        seen[module] = source[module]
    visit(PREFIX + 'KEndpoint215')
    return seen

before = closure(baseline)
after = closure(baseline | overlay)
need(set(before) == {r['module'] for r in snapshot['rows']}, 'baseline closure disagrees')
need(metrics(before) == {'modules': 174, 'bytes': 1752650, 'lines': 37648},
     'unexpected baseline metrics')
need(metrics(after) == {'modules': 168, 'bytes': 1725295, 'lines': 37117},
     'unexpected candidate metrics')

specs = {
 'SingletonInfinity': ('theorem quotientBase', ['FirstOrder.Fol'],
     ['BusyBeaver.ZFC.SingletonInfinityCore', 'BusyBeaver.ZFC.QuotientBasic'],
     '/-- The small base'),
 'FiniteSets': ('theorem quotientBase', ['BusyBeaver.ZFC.SingletonInfinityCore', 'ZF.Zf'],
     ['BusyBeaver.ZFC.FiniteSetsCore', 'BusyBeaver.ZFC.SingletonInfinity'], 'structure Base'),
 'InductiveAttempts': ('theorem quotientFiniteBase',
     ['BusyBeaver.ZFC.SingletonInfinityCore', 'BusyBeaver.ZFC.FiniteSetsCore', 'ZF.Zf'],
     ['BusyBeaver.ZFC.InductiveAttemptsCore', 'BusyBeaver.ZFC.FiniteSets',
      'BusyBeaver.ZFC.QuotientReplacement'], 'def Agree'),
 'WellFoundedPart': ('/-- The actual quotient supplies the fixed native GIC instance and small base. -/',
     ['BusyBeaver.ZFC.FiniteSetsCore', 'BusyBeaver.ZFC.ProfileModel', 'ZF.Zf'],
     ['BusyBeaver.ZFC.WellFoundedPartCore', 'BusyBeaver.ZFC.FiniteSets',
      'BusyBeaver.ZFC.QuotientCPGIC'], 'def NonemptySet'),
}
for name, (marker, ci, wi, header_marker) in specs.items():
    original = baseline[PREFIX + name]
    need(original.count(marker) == 1, 'nonunique boundary: ' + name)
    pre, tail = original.split(marker, 1)
    tail = marker + tail
    body = '\n'.join(line for line in pre.splitlines() if not line.startswith('import '))
    expected_core = '\n'.join('import ' + x for x in ci) + '\n' + body.rstrip() + '\n\nend ' + NS + name + '\n'
    header = pre[pre.index('namespace ' + NS + name):]
    header = header[:header.index(header_marker)]
    expected_wrapper = '\n'.join('import ' + x for x in wi) + '\n\n' + header + tail
    need(overlay[PREFIX + name + 'Core'] == expected_core, 'generic body changed: ' + name)
    need(overlay[PREFIX + name] == expected_wrapper, 'adapter changed: ' + name)
    need('Quotient' not in ''.join(imports(expected_core)), 'legacy core import: ' + name)

substitutions = {
 'WFRelativization': [('import BusyBeaver.ZFC.WellFoundedPart', 'import BusyBeaver.ZFC.WellFoundedPartCore')],
 'KQ1ZF': [('import BusyBeaver.ZFC.InductiveAttempts', 'import BusyBeaver.ZFC.InductiveAttemptsCore')],
 'WFModel': [('import BusyBeaver.ZFC.WFModelCore',
              'import BusyBeaver.ZFC.WFModelCore\nimport BusyBeaver.ZFC.WellFoundedPart')],
 'KLowerQHyp': [('import BusyBeaver.ZFC.QuotientModel', 'import BusyBeaver.ZFC.KQ1Model'),
               ('QuotientModel.memberForm', 'KQ1Model.memberForm'),
               ('QuotientModel.sat_memberForm', 'KQ1Model.sat_memberForm')],
}
for name, edits in substitutions.items():
    expected = baseline[PREFIX + name]
    for old, new in edits:
        need(expected.count(old) == 1, 'nonunique edit: ' + old)
        expected = expected.replace(old, new)
    need(overlay[PREFIX + name] == expected, 'unexpected client edit: ' + name)

quotient = baseline[PREFIX + 'QuotientModel']
need('abbrev memberForm := KQ1Model.memberForm' in quotient, 'memberForm is not a definitional alias')
need('KQ1Model.sat_memberForm mem env i j' in quotient, 'satisfaction forwarding has changed')

expected_removed = {PREFIX + x for x in [
    'SingletonInfinity', 'FiniteSets', 'InductiveAttempts', 'WellFoundedPart',
    'QuotientBasic', 'QuotientCPGIC', 'QuotientModel', 'QuotientPower',
    'QuotientReplacement', 'QuotientSeparation']}
need(set(before) - set(after) == expected_removed, 'unexpected removed modules')
need(not any(m.startswith(PREFIX + 'Quotient') for m in after),
     'legacy CP quotient module remains in selected endpoint')
need(all(PREFIX + x in after for x in ['KQ1Model', 'KQ1Basic', 'KQ1Collect',
       'KQ1Power', 'KQ1Separation', 'KQ1Replacement']), 'generic quotient proof lost')

patch = []
for module, text in sorted(overlay.items()):
    name = module.rsplit('.', 1)[1] + '.lean'
    old = baseline.get(module, '')
    patch.extend(difflib.unified_diff(old.splitlines(True), text.splitlines(True),
        fromfile='a/' + REPO + name if module in baseline else '/dev/null',
        tofile='b/' + REPO + name))
need(''.join(patch) == (HERE / 'generic_spine.patch').read_text(), 'patch is stale')

delta_bytes = sum(len(t.encode()) for t in overlay.values()) - sum(
    len(baseline[m].encode()) for m in overlay if m in baseline)
delta_lines = sum(len(t.splitlines()) for t in overlay.values()) - sum(
    len(baseline[m].splitlines()) for m in overlay if m in baseline)
need((delta_bytes, delta_lines) == (1152, 46), 'maintenance delta changed')

# Scoped producer check: bind the pinned endpoint generator as inert text.
producer = json.loads((HERE / 'generator_review' / 'provenance.json').read_text())
need(producer['pin'] == PIN, 'wrong generator pin')
producer_bytes = (HERE / 'generator_review' / 'generate_endpoints_lean.py.txt').read_bytes()
need(hashlib.sha1(b'blob ' + str(len(producer_bytes)).encode() + b'\0' + producer_bytes).hexdigest()
     == producer['sha'], 'generator Git blob mismatch')
need('(Z / f"KEndpoint{n}.lean").write_text' in producer_bytes.decode(),
     'endpoint generator output pattern changed')
directory = json.loads((HERE / 'formal_directory.json').read_text())
generator_names = sorted(r['name'] for r in directory
                         if r['name'].startswith('generate_') and r['name'].endswith('.py'))
need(len(generator_names) == 32, 'unexpected scoped root generator inventory')
need('generate_kq1.py' not in generator_names, 'retired quotient generator reappeared')

print(json.dumps({
    'status': 'PASS', 'scope': 'Static byte/import/body/patch audit only; no Lean compilation',
    'pin': PIN, 'baseline_bound_sources': len(baseline),
    'before': metrics(before), 'after': metrics(after),
    'selected_savings': {'modules': 6, 'bytes': 27355, 'lines': 531},
    'all_maintained_source_delta': {'modules': 4, 'bytes': delta_bytes, 'lines': delta_lines},
    'removed_from_selected_closure': sorted(expected_removed),
    'new_selected_modules': sorted(set(after) - set(before)),
    'body_preservation': 'All four generic bodies and all eight CP adapter declarations preserved verbatim',
    'selected_endpoint_import_graph_acyclic': True, 'legacy_CP_quotient_imports_in_selected_closure': [],
    'generic_quotient_retained': True,
    'counts_include_only_spine_patch': True,
    'scoped_producer_inventory': {'root_generator_files': 32,
      'retired_generate_kq1_absent': True, 'endpoint_generator_byte_bound': True,
      'repository_wide_producer_search_completed': False},
    'proof_assistant_executed': False,
}, indent=2))
