#!/usr/bin/env python3
"""Read-only source census for the pinned K215 proof-simplification review.

Counts project source imports, not proof terms, compiler work or trusted axioms.
No repository code is imported or executed. Python 3.11+ standard library only.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
TARGET = 'BusyBeaver.ZFC.KEndpoint215'
ZFC = Path('Computability/BusyBeaver/Research/ZFC')

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def uncomment(s: str, opening='/-', closing='-/', line='--') -> str:
    """Preserve strings/newlines, erase nested comments for import parsing."""
    out=[]; i=0; depth=0; quoted=False
    while i < len(s):
        if depth:
            if s.startswith(opening,i): depth+=1; out.extend('  '); i+=2
            elif s.startswith(closing,i): depth-=1; out.extend('  '); i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif quoted:
            out.append(s[i])
            if s[i]=='\\' and i+1<len(s): out.append(s[i+1]); i+=2; continue
            if s[i]=='"': quoted=False
            i+=1
        elif s[i]=='"': quoted=True; out.append(s[i]); i+=1
        elif s.startswith(opening,i): depth=1; out.extend('  '); i+=2
        elif line and s.startswith(line,i):
            j=s.find('\n',i)
            if j<0: j=len(s)
            out.extend(' '*(j-i)); i=j
        else: out.append(s[i]); i+=1
    if depth: raise ValueError('Unclosed comment')
    return ''.join(out)

def source_record(repo: Path, path: Path) -> dict:
    data=path.read_bytes()
    return {'path':str(path.relative_to(repo)), 'bytes':len(data),
            'physical_lines':len(data.splitlines()), 'sha256':sha(data)}

def census(repo: Path, overlay: Path | None=None) -> dict:
    commit=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    if commit!=PIN: raise SystemExit(f'Expected {PIN}, got {commit}')
    config=tomllib.loads((repo/'lakefile.toml').read_text())
    modules={}
    # Scan declared source roots; the root ProveIt library is unnecessary for this target.
    for lib in config['lean_lib']:
        src=lib.get('srcDir')
        if not src: continue
        base=repo/src
        if base.is_dir():
            for p in base.rglob('*.lean'):
                name='.'.join(p.relative_to(base).with_suffix('').parts)
                if name in modules and modules[name]!=p:
                    raise ValueError(f'Ambiguous module {name}')
                modules[name]=p
    original=dict(modules)
    if overlay:
        # The overlay uses repository-relative paths and can add/change files.
        for lib in config['lean_lib']:
            src=lib.get('srcDir')
            if not src: continue
            base=overlay/src
            if base.is_dir():
                for p in base.rglob('*.lean'):
                    modules['.'.join(p.relative_to(base).with_suffix('').parts)]=p
    visited=set(); active=[]; edges={}; toolchain=set()
    def visit(name):
        if name in visited: return
        visited.add(name)
        if name not in modules:
            if name=='Init' or name.startswith(('Init.','Lean.','Std.')) or name in ('Lean','Std'):
                toolchain.add(name); return
            raise ValueError(f'Missing project module {name}: materialize its source root')
        text=uncomment(modules[name].read_text())
        imports=[d for match in re.finditer(r'^\s*import\s+([^\n]+)',text,re.M)
                 for d in match.group(1).split()]
        edges[name]=imports
        for d in imports: visit(d)
        active.append(name)
    visit(TARGET)
    records=[]
    for m in active:
        p=modules[m]; root=overlay if overlay and p.is_relative_to(overlay) else repo
        rec=source_record(root,p)
        rec.update(module=m, origin='overlay' if root==overlay else 'repository', imports=edges[m])
        records.append(rec)
    sites=json.loads((repo/ZFC/'candidate-k215/sites215.json').read_text())
    kinds=Counter(s[1] for s in sites)
    table=(repo/ZFC/'candidate-k215/k215.tm').read_text()
    rows=[l.split() for l in table.splitlines() if l.strip() and not l.startswith('#')]
    machine={'states':len({r[0] for r in rows}),'actions':len(rows),
             'sites':len(sites),'guarded_site_outcomes':len(sites)+kinds['CD'],
             'site_counts':dict(sorted(kinds.items())),
             'maximum_site_depth':max(len(s[0]) for s in sites),
             'table':source_record(repo,repo/ZFC/'candidate-k215/k215.tm'),
             'source':source_record(repo,repo/ZFC/'candidate-k215/sites215.json')}
    result={'repository':'https://github.com/VladimirReshetnikov/ProveIt','commit':commit,
            'target':TARGET,'scope':'transitive syntactic project import closure; comments and blank lines included in physical size; toolchain files excluded',
            'project_modules':len(records), 'source_bytes':sum(x['bytes'] for x in records),
            'physical_lines':sum(x['physical_lines'] for x in records),
            'toolchain_imports':sorted(toolchain), 'machine':machine,
            'modules':records}
    if overlay:
        result['overlay']='repository-relative source overrides'
        result['changed_or_new_modules']=[m for m,p in modules.items() if m not in original or
              (p!=original[m] and p.read_bytes()!=original[m].read_bytes())]
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',required=True,type=Path)
    ap.add_argument('--overlay',type=Path)
    ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args(); result=census(a.repo.resolve(),a.overlay.resolve() if a.overlay else None)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['commit','project_modules','source_bytes','physical_lines','machine']},indent=2))

if __name__=='__main__': main()
