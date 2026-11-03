#!/usr/bin/env python3
"""Source-declared nine-variable build preflight. Does not execute Lean."""
from collections import Counter, deque
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import shutil
import sys
import tomllib

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'lakefile.toml').is_file())
SEED=Path('/tmp/ipra-standard-qm40-author-run-02/lib')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
PROVIDERS=(SEED,PACKAGE,TOOL)
TARGETS=('DiophantineConsistency.IPRANineCurrent','DiophantineConsistency.IPRAExplicitZFCFinal')
lake=tomllib.loads((ROOT/'lakefile.toml').read_text())
libraries={x['name']: ROOT/x.get('srcDir','.') for x in lake.get('lean_lib',[]) if 'name' in x}
libraries.pop('Foundation',None)  # Foundation is supplied by the package provider here.
names=sorted(libraries,key=len,reverse=True)

def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
    if not ok: raise ValueError(msg)

def local(mod):
    for name in names:
        if mod==name or mod.startswith(name+'.'):
            return libraries[name]/('/'.join(mod.split('.'))+'.lean')
    return None

def strip_comments(text):
    """Remove nested Lean block comments, line comments and string contents."""
    out=[];i=0;depth=0;string=False
    while i<len(text):
        two=text[i:i+2];ch=text[i]
        if depth:
            if two=='/-': depth+=1;i+=2;continue
            if two=='-/': depth-=1;i+=2;continue
            if ch=='\n': out.append('\n')
            i+=1;continue
        if string:
            if ch=='\\': i+=2;continue
            if ch=='"': string=False
            if ch=='\n': out.append('\n')
            i+=1;continue
        if two=='/-': out.append(' ');depth=1;i+=2;continue
        if two=='--':
            j=text.find('\n',i)
            if j<0: break
            out.append('\n');i=j+1;continue
        if ch=='"': out.append(' ');string=True;i+=1;continue
        out.append(ch);i+=1
    need(depth==0 and not string,'unterminated comment or string')
    return ''.join(out)

def imports(path):
    found=[]
    for line in strip_comments(path.read_text()).splitlines():
        m=re.match(r'^\s*(?:public\s+)?import\s+([^\n]+)',line)
        if m: found.extend(m.group(1).split())
    need(all(re.fullmatch(r'[\w.]+',x) for x in found),'unsupported import syntax: '+str(path))
    return found

def object_choices(mod):
    relative=Path('/'.join(mod.split('.'))+'.olean')
    return [root/relative for root in PROVIDERS if (root/relative).is_file()]

def graph(target):
    queue=deque([target]);seen={};missing={};external=set()
    while queue:
        mod=queue.popleft()
        if mod in seen or mod in missing or mod in external: continue
        src=local(mod)
        if src is None: external.add(mod);continue
        if not src.is_file(): missing[mod]=str(src);continue
        ds=imports(src)
        seen[mod]={'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'imports':ds}
        queue.extend(ds)
    return seen,missing,external

def snapshot_comparison(module,source,choice):
    # A source next to an object's resolved provider is only a candidate
    # snapshot; its existence does not prove it generated the object.
    real=choice.resolve(strict=True);parts=real.parts
    positions=[i for i,x in enumerate(parts) if x=='lib']
    if not positions: return None
    i=positions[-1]
    candidate=Path(*parts[:i],'src',*parts[i+1:]).with_suffix('.lean')
    if not candidate.is_file(): return None
    return {'module':module,'snapshot':str(candidate),'same_bytes':sha(candidate)==source['source_sha256']}

need(all(p.is_dir() for p in PROVIDERS),'required seed/package/tool root missing')
parts=[];all_seen={};all_missing=set()
for target in TARGETS:
    seen,missing,external=graph(target)
    present={m:object_choices(m) for m in seen}
    absent={m for m,choices in present.items() if not choices}
    external_absent=sorted(m for m in external if not object_choices(m))
    same=[];different=[];unknown=0
    for module,choices in present.items():
        if not choices: continue
        row=snapshot_comparison(module,seen[module],choices[0])
        if row is None: unknown+=1
        elif row['same_bytes']: same.append(row)
        else: different.append(row)
    parts.append({'target':target,'project_sources':len(seen),'missing_project_sources':missing,
                  'present_project_objects':len(seen)-len(absent),'missing_project_objects':len(absent),
                  'missing_by_root':dict(sorted(Counter(m.split('.')[0] for m in absent).items())),
                  'external_direct_leaves':len(external),'missing_external_direct_objects':external_absent,
                  'candidate_snapshot_matches':len(same),'candidate_snapshot_differences':different,
                  'candidate_snapshot_unavailable':unknown})
    for module,entry in seen.items():
        need(module not in all_seen or all_seen[module]==entry,'source changed during traversal: '+module)
        all_seen[module]=entry
    all_missing.update(absent)

# Depth-first topological order with NineCurrent first, followed by the
# remaining ExplicitZFCFinal requirements. This orders only source-declared
# dependencies missing from the candidate provider; it does not assert that
# the provider's present objects correspond to the current sources.
done=set();active=set();order=[]
def visit(module):
    if module in done: return
    need(module not in active,'source import cycle: '+module)
    active.add(module)
    for dependency in all_seen[module]['imports']:
        if dependency in all_seen: visit(dependency)
    active.remove(module);done.add(module)
    if module in all_missing: order.append(module)
for target in TARGETS: visit(target)
for module in sorted(all_missing): visit(module)
need(set(order)==all_missing,'incomplete staged order')
for module in order:
    entry=all_seen[module]
    need(sha(ROOT/entry['source'])==entry['source_sha256'],'staged source changed: '+module)
report={'status':'SOURCE_DECLARED_PREFLIGHT_NOT_A_BUILD',
        'time_utc':datetime.now(timezone.utc).isoformat(), 'repository':str(ROOT),
        'seed':str(SEED),'package':str(PACKAGE),'toolchain_lib':str(TOOL),
        'free_bytes':shutil.disk_usage(ROOT).free,'targets':parts,
        'union_missing_project_objects':len(all_missing),
        'topological_build_order':[{'module':m,**all_seen[m]} for m in order],
        'scope':'Comment-aware source-declared project graph and sampled object availability; '
                'no Lean build, provider/source authentication or package-transitive audit.'}
print(json.dumps(report,indent=2,sort_keys=True))
