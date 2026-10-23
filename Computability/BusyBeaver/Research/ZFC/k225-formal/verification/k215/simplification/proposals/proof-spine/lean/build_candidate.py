#!/usr/bin/env python3
"""Owned, data-only candidate builder. Does not invoke Lean or repository code."""
from pathlib import Path
import difflib
import json
import sys

if not __debug__:
    raise SystemExit('Refuse Python -O: checks must remain enabled.')
HERE = Path(__file__).resolve().parent
CURRENT = HERE / 'current'
OUT = HERE / 'candidate' / 'BusyBeaver' / 'ZFC'
OUT.mkdir(parents=True, exist_ok=True)
NS = 'SetTheory.BusyBeaver.ZFC.'

def need(cond, msg):
    if not cond:
        raise SystemExit(msg)

specs = {
 'SingletonInfinity': ('theorem quotientBase', ['FirstOrder.Fol'],
     ['BusyBeaver.ZFC.SingletonInfinityCore', 'BusyBeaver.ZFC.QuotientBasic']),
 'FiniteSets': ('theorem quotientBase', ['BusyBeaver.ZFC.SingletonInfinityCore', 'ZF.Zf'],
     ['BusyBeaver.ZFC.FiniteSetsCore', 'BusyBeaver.ZFC.SingletonInfinity']),
 'InductiveAttempts': ('theorem quotientFiniteBase',
     ['BusyBeaver.ZFC.SingletonInfinityCore', 'BusyBeaver.ZFC.FiniteSetsCore', 'ZF.Zf'],
     ['BusyBeaver.ZFC.InductiveAttemptsCore', 'BusyBeaver.ZFC.FiniteSets',
      'BusyBeaver.ZFC.QuotientReplacement']),
 'WellFoundedPart': ('/-- The actual quotient supplies the fixed native GIC instance and small base. -/',
     ['BusyBeaver.ZFC.FiniteSetsCore', 'BusyBeaver.ZFC.ProfileModel', 'ZF.Zf'],
     ['BusyBeaver.ZFC.WellFoundedPartCore', 'BusyBeaver.ZFC.FiniteSets',
      'BusyBeaver.ZFC.QuotientCPGIC']),
}
manifest = {'compiled': False, 'ref': 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6', 'moves': []}
for name, (marker, core_imports, wrapper_imports) in specs.items():
    src = (CURRENT / (name + '.lean')).read_text()
    need(src.count(marker) == 1, 'Nonunique boundary: ' + name)
    pre, tail = src.split(marker, 1)
    tail = marker + tail
    body = '\n'.join(line for line in pre.splitlines() if not line.startswith('import '))
    core = '\n'.join('import ' + x for x in core_imports) + '\n' + body.rstrip() + '\n\nend ' + NS + name + '\n'
    start = pre.index('namespace ' + NS + name)
    prefix = pre[start:]
    # Preserve the exact namespace, opens, universe, and variables, not declarations.
    if name == 'SingletonInfinity':
        header_end = prefix.index('/-- The small base')
    elif name == 'FiniteSets':
        header_end = prefix.index('structure Base')
    elif name == 'InductiveAttempts':
        header_end = prefix.index('def Agree')
    else:
        header_end = prefix.index('def NonemptySet')
    wrapper = '\n'.join('import ' + x for x in wrapper_imports) + '\n\n' + prefix[:header_end] + tail
    (OUT / (name + 'Core.lean')).write_text(core)
    (OUT / (name + '.lean')).write_text(wrapper)
    manifest['moves'].append({'original': name, 'core': name + 'Core',
       'boundary': marker, 'generic_body_preserved': body.rstrip() in core,
       'adapter_tail_preserved': tail in wrapper})

for name, substitutions in {
 'WFRelativization': [('import BusyBeaver.ZFC.WellFoundedPart', 'import BusyBeaver.ZFC.WellFoundedPartCore')],
 'KQ1ZF': [('import BusyBeaver.ZFC.InductiveAttempts', 'import BusyBeaver.ZFC.InductiveAttemptsCore')],
 'WFModel': [('import BusyBeaver.ZFC.WFModelCore',
              'import BusyBeaver.ZFC.WFModelCore\nimport BusyBeaver.ZFC.WellFoundedPart')],
 'KLowerQHyp': [('import BusyBeaver.ZFC.QuotientModel', 'import BusyBeaver.ZFC.KQ1Model'),
               ('QuotientModel.memberForm', 'KQ1Model.memberForm'),
               ('QuotientModel.sat_memberForm', 'KQ1Model.sat_memberForm')],
}.items():
    src = (CURRENT / (name + '.lean')).read_text()
    for old, new in substitutions:
        need(src.count(old) == 1, 'Unexpected substitution count: ' + name + ':' + old)
        src = src.replace(old, new)
    (OUT / (name + '.lean')).write_text(src)

patch = []
repo = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
for f in sorted(OUT.glob('*.lean')):
    old = CURRENT / f.name
    old_text = old.read_text().splitlines(True) if old.exists() else []
    patch.extend(difflib.unified_diff(old_text, f.read_text().splitlines(True),
        fromfile='a/' + repo + f.name if old.exists() else '/dev/null',
        tofile='b/' + repo + f.name))
(HERE / 'generic_spine.patch').write_text(''.join(patch))
(HERE / 'move_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('Prepared 12 uncompiled candidate source files; no repository code executed.')
