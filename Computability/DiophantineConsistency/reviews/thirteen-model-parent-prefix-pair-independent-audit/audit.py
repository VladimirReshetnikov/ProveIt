#!/usr/bin/env python3
"""Read-only independent audit of the 20-module paired prefix artifacts."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-parent-prefix'
OUT=Path('/tmp/ipra-thirteen-parent-prefix-pair-01')
SNAP=Path('/tmp/ipra-thirteen-current-source-02')
PARENT=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PARENTMAN=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='4f31021934bd9b9d85d8d734d636fd17b35c953018f2bd13c42dc0236b0e4c42'
DRIVER='881f806b91c37ce596130a19e74a3c605c0ea3c11379f68b1f59bf641dada204'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args):return subprocess.run(['git',*args],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout

def main():
    files=['RESULT.md','terminal-observation.json','pair-receipt.json']
    for side in ('author','peer'):
        files += [str(p.relative_to(PKG)) for p in (PKG/'logs'/side).glob('*.log')]
    need(len(files)==43,'evidence file inventory')
    for name in files:
        p=PKG/name;need(hashlib.sha256(git('show','ac769bfe26:'+p.relative_to(ROOT).as_posix())).hexdigest()==sha(p),'committed evidence '+name)
    need(sha(PKG/'replay.py')==DRIVER and hashlib.sha256(git('show','042c491efa:'+str((PKG/'replay.py').relative_to(ROOT)))).hexdigest()==DRIVER,'driver at launch')
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==98550 and obs['outer_exit_code']==0 and obs['launch_head']=='042c491efa092a8f847971c0d230b8bffe418980' and
         obs['receipt_sha256']==RECEIPT and obs['stdout_final_line']=='PASS_PAIRED_2011_PARENT_PREFIX '+RECEIPT,'observed wrapper')
    need(sha(PKG/'pair-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt bytes')
    r=json.loads((PKG/'pair-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_2011_PARENT_PREFIX' and r['driver_sha256']==DRIVER and len(r['runs'])==40 and len(r['order'])==20,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed input '+path)
    audits=r['independent_audits'];need(len(audits)==2 and audits[0]['status']=='PASS_INDEPENDENT_CORRECTED_SOURCE_FREEZER_AUDIT' and
         audits[1]['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT' and
         audits[1]['workspace_head_at_audit']==obs['launch_head'],'recorded parent audits')
    snapshot=json.loads((SNAP/'manifest.json').read_bytes());parent=json.loads(PARENTMAN.read_bytes())
    need(sha(SNAP/'manifest.json')==r['source_manifest_sha256']=='2b6dc7e05664e925728bfde59e9da4c3d30242a006b1310b1681be53f3b87ef3' and
         len(snapshot['sources'])==44 and len(parent['order'])==70,'manifests')
    # Independently recover the transitive source-declared prefix.
    todo=['DiophantineConsistency.ArithmeticHalfBinomial2011'];seen=set();boundary=set(parent['order'])
    while todo:
        name=todo.pop()
        if name in seen or name in boundary or name in snapshot['external_direct']:continue
        need(name in snapshot['sources'],'unknown import '+name)
        seen.add(name);todo.extend(snapshot['sources'][name]['imports'])
    order=[name for name in snapshot['order'] if name in seen]
    need(order==r['order'] and len(order)==20,'topological prefix')
    expected_guard=set();warnings={};results=[]
    for side,offset in (('author',0),('peer',20)):
        lib=OUT/side/'lib';parentlib=PARENT/side/'child-output/lib';state=json.loads((PARENT/side/'child-output/state.json').read_bytes())
        need(len(state['records'])==70,'parent records')
        for item in state['records']:
            target=parentlib/Path(*item['module'].split('.')).with_suffix('.olean')
            overlay=lib/Path(*item['module'].split('.')).with_suffix('.olean')
            need(item['exit']==0 and sha(target)==item['object_sha256'] and overlay.is_symlink() and
                 overlay.resolve()==target.resolve() and sha(overlay)==item['object_sha256'],'parent overlay '+item['module'])
        available=set(parent['order']);side_warnings=[]
        for i,name in enumerate(order):
            row=r['runs'][offset+i];source=SNAP/snapshot['sources'][name]['snapshot_path'];obj=lib/Path(*name.split('.')).with_suffix('.olean')
            need(row['label']==side and row['module']==name and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None and row['peak_sampled_rss_bytes']>0,'exits '+name)
            need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-3]==str(source) and row['command'][-1]==str(obj),'command '+name)
            need(sha(source)==row['source_sha256']==snapshot['sources'][name]['sha256'] and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'],'source/object '+name)
            imports=snapshot['sources'][name]['imports'];deps={str(PACKAGE/'Init.olean')}
            for dep in imports:
                if dep in available:deps.add(str(lib/Path(*dep.split('.')).with_suffix('.olean')))
                else:
                    need(dep in snapshot['external_direct'],'unavailable import '+dep)
                    deps.add(snapshot['external_direct'][dep]['path'])
            need(set(row['deps_stdout'].splitlines())==deps,'direct deps '+name)
            for dep in deps:
                need(Path(dep).is_file() and dep.endswith('.olean'),'dependency exists')
                stem=dep[:-6]
                expected_guard.update(stem+suffix for suffix in SUFFIXES)
            log=Path(row['log']);tracked=PKG/'logs'/side/log.name
            need(sha(log)==sha(tracked)==row['log_sha256'],'log '+name)
            text=log.read_text();need(not re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',text),'error/admission '+name)
            reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
            need(reports==row['axiom_reports'] and all(set(x.split(', '))<={'propext','Classical.choice','Quot.sound'} for x in reports),'axiom reports '+name)
            side_warnings += [(name,x.split('warning:',1)[1].strip()) for x in text.splitlines() if 'warning:' in x]
            available.add(name)
        need(side_warnings==[('DiophantineConsistency.ArithmeticBinomLegendre',"try 'simp' instead of 'simpa'")],'warning classification '+side)
        warnings[side]=side_warnings
        results.append({'side':side,'parent_objects':70,'compiled_objects':20,'compiler_exits':[0]*20,'direct_deps_exits':[0]*20,'warnings':side_warnings})
    guards=r['guarded_companions'];need(set(guards)==expected_guard and len(guards)==570,'guard coverage')
    for path,value in guards.items():
        p=Path(path)
        if value is None:need(not os.path.lexists(p),'new companion '+path)
        else:need(p.is_file() and str(p.resolve())==value['realpath'] and sha(p)==value['sha256'],'companion '+path)
    for i in range(20):
        x,y=r['runs'][i],r['runs'][i+20]
        need((x['module'],x['source_sha256'],x['object_sha256'],x['log_sha256'])==(y['module'],y['source_sha256'],y['object_sha256'],y['log_sha256']),'sibling match')
    need(all(not x['axiom_reports'] for x in r['runs']),'unexpected axiom print')
    print(json.dumps({'status':'PASS_INDEPENDENT_20_MODULE_PREFIX_PAIR_AUDIT','source_commit':'ac769bfe26',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':98550,'recorded_outer_exit':0,'recorded_launch_head':obs['launch_head'],
      'source_modules':20,'guarded_companions':len(guards),'reports_printed':0,'runs':results,
      'scope':'Read-only paired artifact and direct-guard audit; no Lean rerun, complete axiom inventory, continuous HEAD protection, dynamic/package-transitive provider audit, actual-zero client or iPRA proof.'},indent=2))

if __name__=='__main__':main()
