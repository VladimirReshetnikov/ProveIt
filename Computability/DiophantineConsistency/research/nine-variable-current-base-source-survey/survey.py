#!/usr/bin/env python3
"""Read-only source-declared nine-variable closure against current14 base.

This does not invoke Lean, launch a build, or validate transitive package or
dynamic imports. It writes only JSON to stdout; the caller chooses a receipt.
"""
import contextlib
import hashlib
import io
import json
import os
import runpy
import shutil
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=next(p for p in Path(__file__).resolve().parents if (p/'lakefile.toml').is_file())
research=root/'Computability/DiophantineConsistency/research'
scanner=research/'nine-variable-ipra/bounded-build-preflight/scan.py'
manifest_path=research/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
observation_path=research/'current14-standard-fresh-rebuild-preflight/run-observation.json'
state_path=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
base_lib=Path('/tmp/current14-standard-fresh-build-20261104/lib')
package=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
toolchain=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
pins={scanner:'d72f3242ff991ad537217b8b25c3cde4ab091a06ce45f61d4f92f70886848816',
      manifest_path:'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
      observation_path:'5d45638261f749227f6530b55154b7d3c28197e1e04ab0eaffb10876e2fa3475',
      state_path:'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
for p,h in pins.items():require(p.is_file() and sha(p)==h,'pinned input mismatch '+str(p))
require(all(p.is_dir() for p in (base_lib,package,toolchain)),'missing provider root')
manifest=json.loads(manifest_path.read_text()); observation=json.loads(observation_path.read_text())
state=json.loads(state_path.read_text())
require(state['status']=='PASS' and state['source_status']=='CURRENT_AT_FINAL_CHECK' and
        observation['exit']==0 and observation['build_status']=='PASS' and
        state['manifest_sha256']==pins[manifest_path],'base is not the recorded successful build')

# The pinned scanner is read-only and comment-aware. Its historical-provider
# preflight runs in a captured stdout buffer; only its source graph function
# is used below, with an independently named current base for comparison.
with contextlib.redirect_stdout(io.StringIO()): scan=runpy.run_path(str(scanner))
targets=('DiophantineConsistency.IPRANineCurrent',
         'DiophantineConsistency.IPRANineChecks',
         'DiophantineConsistency.IPRAExplicitZFCFinal')
all_seen={}; external=set(); per_target={}
for target in targets:
    seen,missing,ext=scan['graph'](target)
    require(not missing,'missing project sources '+repr(missing))
    for name,rec in seen.items():
        require(name not in all_seen or all_seen[name]==rec,'source changed between traversals '+name)
        all_seen[name]=rec
    external.update(ext);per_target[target]={'project_sources':len(seen),'declared_external':len(ext)}

base=manifest['sources']; shared=sorted(set(all_seen)&set(base)); extension=set(all_seen)-set(base)
for name in shared:
    require(all_seen[name]['source_sha256']==base[name]['sha256'] and
            all_seen[name]['imports']==base[name]['imports'],'base source or declared-import drift '+name)
records={r['module']:r for r in state['records']}
verified_direct_paths={}; direct_edges=0
for name in shared:
    require(name in state['outputs'] and name in records and records[name]['exit']==0,
            'missing successful base record '+name)
    outputs=state['outputs'][name]
    for raw,entry in outputs.items():
        p=Path(raw)
        if entry is None:require(not os.path.lexists(p),'unexpected base companion '+raw)
        else:require(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],
                     'base object or companion mismatch '+raw)
    recorded=records[name]['direct_inputs']
    require(set(recorded)-{'Init'}==set(all_seen[name]['imports'])-{'Init'},
            'base recorded direct-input names differ from declared imports '+name)
    for dep,entry in recorded.items():
        p=Path(entry['path']);expected=entry['sha256'];direct_edges+=1
        require(str(p) not in verified_direct_paths or verified_direct_paths[str(p)]==expected,
                'one recorded direct path has conflicting hashes '+str(p))
        if str(p) not in verified_direct_paths:
            require(p.is_file() and sha(p)==expected,'base direct input drift '+str(p))
            verified_direct_paths[str(p)]=expected

active=set();done=set();order=[]
def visit(name):
    if name in done:return
    require(name not in active,'source-declared cycle '+name);active.add(name)
    for dep in all_seen[name]['imports']:
        if dep in all_seen:visit(dep)
    active.remove(name);done.add(name)
    if name in extension:order.append(name)
for name in targets:visit(name)
require(set(order)==extension and len(order)==len(extension),'extension order incomplete')
positions={name:i for i,name in enumerate(order)}
for name in order:
    for dep in all_seen[name]['imports']:
        if dep in extension:require(positions[dep]<positions[name],'invalid dependency order')
for name,rec in all_seen.items():
    require(sha(root/rec['source'])==rec['source_sha256'],'workspace source changed '+name)

new_external=sorted(external-set(manifest['external_modules']))
provider_records={}
for name in sorted(external|{'Init'}):
    rel=Path(*name.split('.')).with_suffix('.olean')
    candidates=[]
    for provider in (package,toolchain):
        p=provider/rel
        if p.is_file():candidates.append({'path':str(p),'realpath':str(p.resolve()),'sha256':sha(p)})
    provider_records[name]=candidates
missing_external=[name for name,choices in provider_records.items() if not choices]
ambiguous_external=[name for name,choices in provider_records.items() if len(choices)>1 and
                    len({c['sha256'] for c in choices})>1]
matrix_names=('Foundation.Vorspiel.Matrix','Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber')
result={'status':'SOURCE_DECLARED_SURVEY_NOT_A_BUILD',
 'git_head':__import__('subprocess').run(['git','rev-parse','HEAD'],cwd=root,check=True,capture_output=True,text=True).stdout.strip(),
 'targets':per_target,'project_count':len(all_seen),'shared_base_count':len(shared),
 'shared_base_recorded_direct_edges_checked':direct_edges,
 'shared_base_distinct_direct_input_paths_checked':len(verified_direct_paths),
 'extension_count':len(order),'shared_base_modules':shared,'extension_order':order,
 'project_sources':dict(sorted(all_seen.items())),
 'declared_external':sorted(external),'new_declared_external':new_external,
 'external_provider_candidates':provider_records,'missing_external':missing_external,
 'different_hash_multiple_provider_candidates':ambiguous_external,
 'matrix_direct_leaf_presence':{x:(x in external) for x in matrix_names},
 'matrix_risk':'UNRESOLVED: declared direct leaves omit package-transitive and dynamic imports; independently inspect both Matrix declarations and provider paths before any combined build.',
 'free_bytes':shutil.disk_usage(root).free,'base_manifest_sha256':pins[manifest_path],
 'base_state_sha256':pins[state_path],
 'scope':'Current source-declared graph and base-object rehash, not Lean --deps, a frozen filesystem snapshot, independent package rebuild, or a proof of future build compatibility.'}
for p,h in pins.items():require(sha(p)==h,'pinned input changed during survey '+str(p))
print(json.dumps(result,indent=2,sort_keys=True))
