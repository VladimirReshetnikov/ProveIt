#!/usr/bin/env python3
"""Read-only paired free-J power growth audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-power-growth-prototype'
PARENT=BASE/'reviews/ordinary12-freej-power-projection-independent-audit'
OUT=Path('/tmp/ipra-freej-power-growth-pair-01')
PRIOR=Path('/tmp/ipra-freej-power-projection-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='e87b5ae91986a25cbdaa50feb764be74a1b934047bda4d9ff8669bd44d72392a'
AUDIT='6317f839a8ebd245a585c17acaec8b1759da3ce5ca172ea75a7a27ea42f38818'
SOURCE='9f63535145100f8c55c39be31db3d4609ecca076821678d8d668b0b984dbb320'
SEED='bff8f46bce63d3e960d243a77f8901b340f7a66c7492983494abe5b22ecb1014'
OBJECT='9af4fef061a9864c06240a5fd90826c0c8f58ea3a2f726fff49e6318324da15d'
LOG='b9135b8d487efd515de3b0663538b838fb35668992c6ce4bcce3f010e309d438'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJPowerGrowth.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.txt','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','f82be9b81b:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=(PKG/'evidence/terminal.txt').read_text()
    need('Actual outer wrapper session 78120 exited 0.' in obs and
         'PASS_PAIRED_FREEJ_POWER_GROWTH '+RECEIPT in obs,'outer observation')
    for f in (PKG/'observations/attempt01.log',PKG/'observations/attempt01.lean',PKG/'observations/attempt02.log',PKG/'observations/attempts.txt'):
        blob=subprocess.run(['git','show','f82be9b81b:'+str(f.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(f),'exploratory committed bytes')
    need('error:' in (PKG/'observations/attempt01.log').read_text() and 'sorryAx' in (PKG/'observations/attempt01.log').read_text() and
         not re.search(r'warning:|error:|sorryAx', (PKG/'observations/attempt02.log').read_text()),'exploratory observations')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_POWER_GROWTH' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJPowerGrowth.lean';obj=run/'FreeJPowerGrowth.olean';seed=proj/'FreeJPowerProjection.olean'
        need(sha(src)==sha(PKG/'FreeJPowerGrowth.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJPowerProjection.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==89 and links==parentfiles,'parent coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PRIOR/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver link')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed),str(proj/'ArithmeticPellPowerRecovery.olean')},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        reports=re.findall(r"^'FreeJPowerGrowth\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['X_lower','growth'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*2 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':89,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_POWER_GROWTH_AUDIT','source_commit':'f82be9b81b',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':78120,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, power identity, cancellation, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
