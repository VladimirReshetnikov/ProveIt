#!/usr/bin/env python3
"""Point-in-time post-run manifest and source check; no Lean invocation."""
import ast
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
HERE=Path(__file__).resolve().parent
EXPECTED='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded'
REPO=BASE/'research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay/source-freeze-evidence-03/manifest.json'
SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-03')
AUDIT=BASE/'reviews/ordinary12-coexistence-pair-independent-audit/CHECK.json'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    need(digest(REPO)==digest(SNAP/'manifest.json')==EXPECTED,'post-run manifest digest')
    parent=json.loads(AUDIT.read_bytes());need(parent['source_manifest_sha256']==EXPECTED and parent['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT','audited parent manifest')
    m=json.loads(REPO.read_bytes());names=m['order'];need(len(names)==70 and len(set(names))==70,'source count')
    for name in names:
        row=m['sources'][name];need(digest(SNAP/row['snapshot_path'])==digest(ROOT/row['workspace_path'])==row['sha256'],'source '+name)
    source=(HERE/'monitor-final-c5.py').read_bytes()
    need(hashlib.sha256(source).hexdigest()=='c5cc9ec88c7c7cf7b6ec47b26281259c698dbadbb7c87a96b68433e3bcb5d3b0','driver snapshot')
    assignments=[x for x in ast.parse(source).body if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='SOURCES' for t in x.targets)]
    need(len(assignments)==1,'driver source pins');rows=ast.literal_eval(assignments[0].value)
    for rel,h,_ in rows:need(digest(BASE/'research/ordinary12-ipra-bridge'/rel)==h,'suffix source '+rel)
    head=subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,capture_output=True,text=True,check=True).stdout.strip()
    print(json.dumps({'status':'PASS_POST_RUN_MANIFEST_AND_SOURCE_OBSERVATION','observed_utc':datetime.now(timezone.utc).isoformat(),
      'repository_manifest_sha256':EXPECTED,'frozen_manifest_sha256':EXPECTED,'parent_audit_manifest_sha256':parent['source_manifest_sha256'],
      'matching_frozen_and_workspace_sources':len(names),'matching_driver_suffix_sources':len(rows),'observed_head':head,
      'scope':'Only this post-run instant. The live driver did not pin its manifest read; exact execution-time bytes and changes between observations are not established.'},indent=2))


if __name__=='__main__':main()
