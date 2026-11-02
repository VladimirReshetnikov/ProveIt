#!/usr/bin/env python3
"""Read-only audit of the graph/independent signed-integrality join."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
BRIDGE=BASE/'research/ordinary12-ipra-bridge'
PKG=BRIDGE/'free-j-graph-integrality-prototype'
GRAPH=BRIDGE/'free-j-current-denominator-composition'
GAUDIT=BASE/'reviews/ordinary12-current-denominator-independent-audit'
SAUDIT=BASE/'reviews/ordinary12-reduced-model-signed-independent-audit'
OUT=Path('/tmp/ipra-freej-graph-integrality-pair-01')
GRUN=Path('/tmp/ipra-freej-current-denominator-rebuild-04')
SRUN=Path('/tmp/ipra-reduced-model-signed-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='61b12fb93bc50e43ee710b3bac6a1d40cb61f1af1a6fbe3f9861985a06d3dc9d'
SOURCE='8837d4f9d83f4b9500a99c5c2ed7cca521b4fd383362d1a660eea45fe2e3fd22'
OBJECT='826781b0eec49929248439fc8b5fd71c9d788b99b21bd1fbcd5c21ab2c865a39'
LOG='b8cc21adc68dac742acfc1227454086d67ee18c0cea1fef438202ca6418874a4'
GAUDITH='5c660c74ddd281fcfafbca9c993e0b53945f30d2322e5216a0f42e8e5d27ee16'
SAUDITH='2f65a3ebbde03f2d894ee88608c41a2d83eb033f7e485d523e95bd71462de09d'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    for p in [PKG/'replay.py',PKG/'FreeJGraphIntegrality.lean',*(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','251ff2dc82:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==87494 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_GRAPH_DIVISIBILITY' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(GAUDIT/'CHECK.json')==GAUDITH and sha(SAUDIT/'CHECK.json')==SAUDITH,'independent parent audit pins')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(SAUDIT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((SAUDIT/'CHECK.json').read_bytes()),'signed parent re-audit')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(GAUDIT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==1 and b'committed author packet drift' in p.stderr,'graph parent guard observation')
    drift=subprocess.run(['git','diff','--name-only','d40b6397f5','--',str(GRAPH.relative_to(ROOT))],cwd=ROOT,check=True,capture_output=True,text=True).stdout.splitlines()
    need(drift==[str((GRAPH/'README.md').relative_to(ROOT))],'graph parent README-only drift')
    graph=json.loads((GRAPH/'evidence/receipt.json').read_bytes())
    need(sha(GRAPH/'evidence/receipt.json')=='a9517710d23a1576f04610ef00f3e16038086eed2956fddc2cd0cf76f006ef7b' and len(graph['runs'])==24,'graph receipt')
    for item in graph['runs']:
        src=Path(item['command'][-3]);obj=Path(item['command'][-1]);log=Path(item['log'])
        need(item['exit']==item['deps_exit']==0 and sha(src)==item['source_sha256'] and sha(obj)==item['object_sha256'] and sha(log)==item['log_sha256'],'graph parent row')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=GRUN/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJGraphIntegrality.lean';obj=run/'FreeJGraphIntegrality.olean'
        need(sha(src)==sha(PKG/'FreeJGraphIntegrality.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        priorfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(links==priorfiles,'graph overlay coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'graph overlay '+name)
        joined=row['joined_seed_sha256'];need(len(joined)==7 and set(joined).isdisjoint({Path(x).stem for x in priorfiles}),'signed seed collision')
        for name,h in joined.items():
            seed=proj/(name+'.olean');parent=(SRUN/side/'ReducedNormSigned.olean' if name=='ReducedNormSigned' else SRUN/side/'lib/DiophantineConsistency'/(name+'.olean'))
            need(not seed.is_symlink() and sha(seed)==sha(parent)==h,'signed seed '+name)
        bb=run/'lib/BusyBeaver';priorbb=GRUN/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(proj/'FreeJCurrentDenominator.olean'),str(proj/'ReducedNormSigned.olean')},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'log')
        reports=re.findall(r"^'FreeJGraphIntegrality\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graphQ_eval','graph_denominator_divides'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*2 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'graph_overlay_links':len(links),'signed_seed_count':len(joined),'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_GRAPH_INTEGRALITY_AUDIT','source_commit':'251ff2dc82',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':87494,'recorded_outer_exit':0,
      'graph_parent_audit_sha256':GAUDITH,'graph_parent_rerun_exit':1,'graph_parent_rerun_reason':'broad historical guard detects subsequent README-only edit',
      'graph_source_object_log_rows_checked':24,'signed_parent_audit_sha256':SAUDITH,'signed_parent_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired join audit; no Lean rerun, ordinary strong norm, checker calibration or object-level iPRA proof.'},indent=2))

if __name__=='__main__':main()
