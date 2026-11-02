#!/usr/bin/env python3
"""Low-I/O declared import survey for the uncompiled standard AQ29 client.

The parent manifest is used without re-reading its source bytes. The result is
planning evidence only, not Lean dependency resolution or a proof replay.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PARENT = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PIN = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
PLANNER = ROOT/'Computability/DiophantineConsistency/research/reference-coherent-replay/plan.py'
TARGET = 'DiophantineConsistency.IPRAStandardAQ29Checks'

raw = (PARENT/'manifest.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != PIN:
    raise ValueError('parent manifest pin differs')
parent = json.loads(raw)
spec = importlib.util.spec_from_file_location('reference_plan', PLANNER)
planner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(planner)
cfg = tomllib.loads((ROOT/'lakefile.toml').read_text())
libs = {x['name']: ROOT/x.get('srcDir', '.') for x in cfg['lean_lib']}
libs.pop('Foundation', None)
drafts = {f'DiophantineConsistency.{name}': HERE/'draft'/(name+'.lean')
          for name in ('IPRAStandardAQ29', 'IPRAStandardAQ29Checks')}
result = planner.plan(ROOT, PARENT, parent, libs, [TARGET], drafts, 'historical', True)
paths = [result['sources'][name]['workspace_path'] for name in result['additional_project_modules']]
tracked = subprocess.check_output(['git', 'ls-files', '-z', '--', *paths], cwd=ROOT).split(b'\0')
modified = subprocess.check_output(['git', 'diff', '--name-only', '-z', 'HEAD', '--', *paths], cwd=ROOT).split(b'\0')
result.update(parent_manifest_sha256=PIN, planner_sha256=planner.sha(PLANNER.read_bytes()),
              survey_sha256=planner.sha(Path(__file__).read_bytes()),
              workspace_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              additional_untracked=sorted(set(paths)-{p.decode() for p in tracked if p}),
              additional_modified_against_head=sorted(p.decode() for p in modified if p))
used = result.pop('parent_source_modules_used')
additions = result['additional_project_modules']
result['parent_modules_used'] = len(used)
result['parent_module_order_sha256'] = planner.sha(('\n'.join(used)+'\n').encode())
result['parent_modules_not_used'] = sorted(set(parent['order'])-set(used))
result['direct_external_not_in_parent'] = sorted(set(result['external_modules'])-set(parent['external_modules']))
result['sources'] = {name: result['sources'][name] for name in additions}
result.pop('order')
output = HERE/'survey-receipt.json'
if output.exists() or output.is_symlink():
    raise ValueError('refusing to overwrite existing receipt')
output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(result['status'], result['parent_modules_used'], 'parent modules;',
      len(result['additional_project_modules']), 'additional modules;',
      'parent bytes and drift unchecked;', planner.sha(output.read_bytes()))
