#!/usr/bin/env python3
"""Verify the pinned freezer, source snapshot, and 338 source anchor blobs."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-endpoint-successor'
PLAN=BASE/'research/thirteen-model-endpoint-closure'
SNAP=Path('/tmp/ipra-thirteen-endpoint-source-01')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/'
    names=subprocess.run(['git','ls-tree','-r','--name-only','3a03b220a6','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(names)==8,'committed packet inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','3a03b220a6:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==H(p),'committed bytes '+name)
    need(H(PKG/'replay.py')=='a97d57a3290d85025699136b8d547a12c0cb9e90aba482595d0da6fac82e6428','launcher hash')
    need(H(SNAP/'manifest.json')==H(PKG/'frozen-manifest.json')=='5be9ded1c401d511b8be4d34d3bcc7c71fc04929f9b43502bb92281827032778','snapshot manifest')
    m=json.loads((SNAP/'manifest.json').read_bytes());plan=json.loads((PLAN/'frontier-plan.json').read_bytes());survey=json.loads((PLAN/'source-manifest.json').read_bytes())
    need(H(PKG/'freeze.py')==m['freezer_sha256'],'freezer provenance')
    need(m['source_anchor']==survey['source_anchor']=='ca2b5071e3c647e4bf3039ac52e4308a179dcfa6' and m['frontier_plan_sha256']==H(PLAN/'frontier-plan.json') and m['source_manifest_sha256']==H(PLAN/'source-manifest.json'),'plan binding')
    need(m['status']=='FROZEN_338_SOURCE_FRONTIER_NOT_COMPILED' and m['order']==plan['rebuild_order'] and m['reusable_seeds']==plan['reusable_seeds'] and len(m['order'])==len(m['sources'])==338 and set(m['order'])==set(m['sources']) and len(m['reusable_seeds'])==807,'inventory')
    for n,row in m['sources'].items():
        path=SNAP/row['snapshot_path'];expected=SNAP/'src'/Path(*n.split('.')).with_suffix('.lean');workspace=ROOT/row['workspace_path']
        need(path==expected and path.is_file() and not path.is_symlink() and H(path)==H(workspace)==row['sha256']==plan['all_selected_source_hashes'][n],'frozen/workspace '+n)
        blob=subprocess.run(['git','show',m['source_anchor']+':'+row['workspace_path']],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==row['sha256'],'anchor '+n)
    print(json.dumps({'status':'PASS_INDEPENDENT_338_SOURCE_SNAPSHOT','commit':'3a03b220a6','snapshot_manifest_sha256':H(SNAP/'manifest.json'),'freezer_sha256':H(PKG/'freeze.py'),'launcher_sha256':H(PKG/'replay.py'),'source_anchor':m['source_anchor'],'sources_checked':len(m['sources']),'seed_names':len(m['reusable_seeds']),'scope':'Read-only source snapshot provenance; no Lean build or continuous mutation protection.'},indent=2))
if __name__=='__main__':main()
