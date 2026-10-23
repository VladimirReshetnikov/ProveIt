#!/usr/bin/env python3
"""Exact static import/source census for the pinned maintained Lean endpoint.

This does not compile or reuse any proof object. Historical receipt hashes are
compared only to expose source drift, never to certify the changed endpoint.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


ROOTS = {
    'BusyBeaver': 'Computability/BusyBeaver/Lean',
    'FirstOrder': 'Logic/FirstOrder/Lean',
    'ZF': 'SetTheory/ZF/Lean',
    'BoundedZFCConsistency': 'SetTheory/BoundedConsistency/Lean',
}


def imports(text):
    # A nested block-comment eraser suffices for these source headers. Verify
    # no unclosed comment and only collect syntactic header lines.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; i += 2
        else:
            if not depth or text[i] == '\n':
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    result=[]
    for line in ''.join(out).splitlines():
        line=line.split('--',1)[0]
        m=re.match(r'^\s*(?:public\s+|private\s+)?import\s+(.+?)\s*$',line)
        if m:
            result.extend(m.group(1).split())
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    repo=a.repo.resolve()
    pending=['BusyBeaver.ZFC.KEndpoint215']; found={}; external=set()
    while pending:
        mod=pending.pop()
        if mod in found or mod in external:
            continue
        prefix=mod.split('.')[0]
        if prefix not in ROOTS:
            if prefix not in ('Init','Lean','Std'):
                raise ValueError('Unknown project-module root: '+mod)
            external.add(mod);continue
        path=repo/ROOTS[prefix]/(mod.replace('.','/')+'.lean')
        raw=path.read_bytes();text=raw.decode('utf-8');deps=imports(text)
        found[mod]=dict(path=str(path.relative_to(repo)),sha256=hashlib.sha256(raw).hexdigest(),
                        bytes=len(raw),physical_lines=len(text.splitlines()),imports=deps)
        pending.extend(deps)
    reference=repo/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15/integration/current-review.json'
    old=json.loads(reference.read_text())['sources']
    changed=[];new=[]
    for mod,info in sorted(found.items()):
        if mod not in old:new.append(mod)
        elif old[mod]['sha256']!=info['sha256']:
            changed.append(dict(module=mod,phase15_sha256=old[mod]['sha256'],current_sha256=info['sha256']))
    output=dict(status='PASS_STATIC_CURRENT_IMPORT_CENSUS',
                commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
                root='BusyBeaver.ZFC.KEndpoint215',project_modules=len(found),
                source_bytes=sum(x['bytes']for x in found.values()),
                physical_lines=sum(x['physical_lines']for x in found.values()),
                external_toolchain_imports=sorted(external),
                historical_phase15_documented_endpoint=dict(project_modules=176,source_bytes=2052142,
                    status='Historical documented checkpoint; not a current-source census'),
                current_vs_phase15_hashes=dict(reference=str(reference.relative_to(repo)),
                    reference_sha256=hashlib.sha256(reference.read_bytes()).hexdigest(),
                    changed_current_endpoint_modules=changed,new_current_endpoint_modules=new),
                sources=dict(sorted(found.items())),
                scope='Static source import closure only; no proof compilation or endpoint recertification.')
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items()if k not in ('sources','current_vs_phase15_hashes')},indent=2))
    print(json.dumps(dict(changed_from_phase15=[x['module']for x in changed],new_to_phase15=new),indent=2))


if __name__=='__main__':main()
