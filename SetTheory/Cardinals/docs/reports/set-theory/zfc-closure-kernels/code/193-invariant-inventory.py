#!/usr/bin/env python3
"""Inventory explicitly imported project sources, not kernel theorem dependencies.

Requires Python 3.11+ for tomllib. The import scanner is scoped to the ordinary
single-line import syntax used by this pinned endpoint closure.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--out', type=Path, required=True)
p.add_argument('--endpoint', default='BusyBeaver.ZFC.KEndpoint215')
a = p.parse_args()
repo = a.repo.resolve()
config = tomllib.loads((repo / 'lakefile.toml').read_text())
roots = sorted({repo / x.get('srcDir', '.') for x in config['lean_lib']})
project_names = {x['name'] for x in config['lean_lib']}
seen, external = {}, set()

def visit(name):
    if name in seen or name in external:
        return
    rel = Path(*name.split('.')).with_suffix('.lean')
    paths = [root / rel for root in roots if (root / rel).is_file()]
    if len(paths) > 1:
        raise RuntimeError(f'Ambiguous source for {name}: {paths}')
    if not paths:
        if name.split('.')[0] in project_names:
            raise FileNotFoundError(f'Missing project source: {name}')
        external.add(name)
        return
    path = paths[0]
    data = path.read_bytes()
    text = data.decode('utf-8')
    imports = []
    for line in text.splitlines():
        match = re.match(r'^(?:public\s+)?import\s+([\w.\s]+?)(?:\s*--.*)?$', line)
        if match:
            imports.extend(match.group(1).split())
    seen[name] = {'module': name, 'path': str(path.relative_to(repo)),
                  'bytes': len(data), 'lines': len(text.splitlines()),
                  'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports}
    for dependency in imports:
        visit(dependency)

visit(a.endpoint)
modules = [seen[name] for name in sorted(seen)]
report = {
    'head': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
    'endpoint': a.endpoint,
    'method': 'Static import closure including endpoint; project source roots from lakefile.toml. No build or kernel dependency extraction.',
    'module_count': len(modules), 'total_bytes': sum(x['bytes'] for x in modules),
    'total_lines': sum(x['lines'] for x in modules),
    'external_direct_modules': sorted(external), 'modules': modules,
}
a.out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'modules'}))
