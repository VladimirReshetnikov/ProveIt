#!/usr/bin/env python3
"""Audit the corrected frozen source extension and test a fresh freezer run."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-parent-current-closure'
AUDIT=BASE/'reviews/thirteen-model-parent-current-closure-independent-audit'
ONE=Path('/tmp/ipra-thirteen-current-source-01')
TWO=Path('/tmp/ipra-thirteen-current-source-02')
HASH='2b6dc7e05664e925728bfde59e9da4c3d30242a006b1310b1681be53f3b87ef3'
FREEZER='af6d6c4897916c7738fb7b5e18633843f8a74dd68a75e6fa26fd0d89c148214f'
AUDITH='c2902ee276a1c1dc5c1aaa05015758bf1e9966b79537a1ec53fcea3cc69b48c9'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args):return subprocess.run(['git',*args],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout

def main():
    for name in ('README.md','FREEZE.md','freeze.py','freeze-observation.json','freeze-retry-observation.json','source-manifest.json','frozen-manifest.json'):
        p=PKG/name;need(hashlib.sha256(git('show','76408407a0:'+p.relative_to(ROOT).as_posix())).hexdigest()==sha(p),'corrected committed bytes '+name)
    need(sha(PKG/'freeze.py')==FREEZER and sha(AUDIT/'CHECK.json')==AUDITH,'fixed audit and freezer bytes')
    survey=subprocess.run([sys.executable,'-I','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=180)
    need(survey.returncode==0 and not survey.stderr and json.loads(survey.stdout)==json.loads((AUDIT/'CHECK.json').read_bytes()),'restored survey independent audit')
    m=json.loads((PKG/'frozen-manifest.json').read_bytes());plan=json.loads((PKG/'source-manifest.json').read_bytes())
    need(m['status']=='FROZEN_44_SOURCE_EXTENSION_NOT_COMPILED' and len(m['sources'])==44 and
         m['independent_audit_sha256']==AUDITH and m['source_manifest_sha256']==sha(PKG/'source-manifest.json') and
         m['source_anchor']==plan['source_anchor'] and m['order']==plan['order'] and
         m['direct_parent_boundary']==plan['direct_parent_boundary'] and m['external_direct']==plan['external_direct'],'snapshot metadata')
    need(sha(PKG/'frozen-manifest.json')==sha(ONE/'manifest.json')==sha(TWO/'manifest.json')==HASH,'snapshot manifests')
    for obsfile,session,path in [('freeze-observation.json',92246,ONE),('freeze-retry-observation.json',47339,TWO)]:
        obs=json.loads((PKG/obsfile).read_bytes())
        need(obs['session_id']==session and obs['outer_exit_code']==0 and obs['manifest_sha256']==HASH and
             obs['freezer_sha256']==FREEZER and obs['output']==str(path) and obs['stdout']=='PASS_FROZEN_44_SOURCE_EXTENSION '+HASH,'actual observation')
    for name,row in m['sources'].items():
        ref=plan['sources'][name];rel=row['workspace_path'];dest=Path(row['snapshot_path'])
        need(not dest.is_absolute() and '..' not in dest.parts and row['imports']==ref['imports'] and rel==ref['workspace_path'] and row['sha256']==ref['sha256'],'row '+name)
        src=ROOT/rel;blob=git('show',m['source_anchor']+':'+rel)
        need(sha(src)==hashlib.sha256(blob).hexdigest()==row['sha256'],'source bytes '+name)
        for root in (ONE,TWO):
            f=root/dest;need(f.is_file() and not f.is_symlink() and sha(f)==row['sha256'],'snapshot '+name)
    expected={row['snapshot_path'] for row in m['sources'].values()}
    for root in (ONE,TWO):need({str(p.relative_to(root)) for p in (root/'src').rglob('*.lean')}==expected,'snapshot source inventory')
    observations=m['source_audit_observations']
    need(len(observations)==2 and all(x['exit']==0 and not x['stderr'] for x in observations) and
         json.loads(observations[1]['stdout'])==json.loads((AUDIT/'CHECK.json').read_bytes()),'recorded source checks')
    opt=subprocess.run([sys.executable,'-I','-S','-O',str(PKG/'freeze.py'),'--output',str(TWO)],capture_output=True,timeout=30)
    need(opt.returncode!=0 and b'source freezer rejects optimized Python' in opt.stderr,'optimized guard')
    collision=subprocess.run([sys.executable,'-I','-S',str(PKG/'freeze.py'),'--output',str(TWO)],capture_output=True,timeout=30)
    need(collision.returncode!=0 and b'output already exists' in collision.stderr,'overwrite guard')
    new=Path(tempfile.mkdtemp(prefix='ipra-thirteen-current-source-independent-',dir='/tmp'))
    new.rmdir()  # Reserve a randomized name, then satisfy the freezable fresh-path precondition.
    try:
        retry=subprocess.run([sys.executable,'-I','-S',str(PKG/'freeze.py'),'--output',str(new)],capture_output=True,timeout=180)
        need(retry.returncode==0 and not retry.stderr and retry.stdout.decode().strip()=='PASS_FROZEN_44_SOURCE_EXTENSION '+HASH and sha(new/'manifest.json')==HASH,'fresh freezer replay')
        for row in m['sources'].values():need(sha(new/row['snapshot_path'])==row['sha256'],'fresh snapshot')
    finally:
        if new.exists():shutil.rmtree(new)
    print(json.dumps({'status':'PASS_INDEPENDENT_CORRECTED_SOURCE_FREEZER_AUDIT','source_commit':'76408407a0',
      'freezer_sha256':FREEZER,'manifest_sha256':HASH,'first_recorded_outer_session':92246,'retry_recorded_outer_session':47339,
      'recorded_outer_exits':[0,0],'independent_survey_rerun_exit':0,'optimized_guard_exit':opt.returncode,
      'collision_guard_exit':collision.returncode,'fresh_freezer_exit':retry.returncode,'verified_sources':44,
      'scope':'Source snapshot and freezer control audit only; no Lean build, process runtime guard, package-transitive/dynamic provider audit, or iPRA proof.'},indent=2))

if __name__=='__main__':main()
