#!/usr/bin/env python3
"""Retain the checked component builders in private, disjoint directories."""
import os
from pathlib import Path
import re
import sys

if len(sys.argv) != 2:
    raise SystemExit('usage: prepare_components.py OUTPUT_DIR')
root = Path('Computability/BusyBeaver/Research/PA')
out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
components = {
    'coverage': ('pa194-coverage/check.sh', '$task_dir/PA194CoverageComplete.lean',
                 '$task_dir/PA194CoverageComplete.olean'),
    'startup': ('pa194-startup/check.sh', '$task_dir/PA194StartupComplete.lean',
                '$task_dir/PA194StartupComplete.olean'),
    'dense': ('pa194-dense/check.sh', '$base/pa194-dense/PA194DenseGlobal.lean',
              '$task_dir/PA194DenseGlobal.olean'),
    'zip': ('pa194-zip-bridge/check.sh',
            'Computability/BusyBeaver/Research/PA/pa194-zip-bridge/PA194ZipRun.lean',
            '$task_dir/PA194ZipRun.olean'),
    'parent': ('pa194-parent-zip/check.sh', '$base/pa194-parent-zip/PA194ParentZip.lean',
               '$task_dir/PA194ParentZip.olean'),
    'clock': ('pa194/ipra/machine-code/check-endpoint.sh', None, None),
}
for name, (rel, source, target) in components.items():
    text = (root / rel).read_text()
    text, n = re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$',
                      'task_dir=$PA194_COMPONENT_DIR', text, count=1, flags=re.M)
    if n != 1:
        raise SystemExit(f'{rel}: task directory declaration changed')
    old_trap = "trap 'rm -rf \"$task_dir\"' EXIT"
    if text.count(old_trap) != 1:
        raise SystemExit(f'{rel}: cleanup declaration changed')
    text = text.replace(old_trap, '', 1)
    repo_line = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
    text = text.replace(repo_line, 'repo=$(pwd)')
    if name == 'clock':
        marker = 'lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PackedRootModel.lean'
        if text.count(marker) != 1:
            raise SystemExit(f'{rel}: PackedStandard boundary changed')
        text = text[:text.index(marker)] + '''if rg -q "sorryAx" "$BINARY_TAPE_TASK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'\n'''
    else:
        quoted = f'"{source}"' if source.startswith('$') else source
        lines = text.splitlines(keepends=True)
        matches = [i for i, line in enumerate(lines) if 'lean ' in line and quoted in line]
        if len(matches) != 1:
            raise SystemExit(f'{rel}: final aggregate invocation changed')
        i = matches[0]
        root_arg = '--root="$task_dir" ' if name in ('coverage', 'startup') else ''
        lines[i] = lines[i].replace(quoted, f'{root_arg}-o "{target}" {quoted}', 1)
        text = ''.join(lines)
    path = out / f'{name}.sh'
    path.write_text(text)
    os.chmod(path, 0o755)
