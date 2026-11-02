#!/usr/bin/env python3
"""Independently inspect the paired model descent suffix without running Lean."""
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
PKG = BASE / 'research/ordinary12-ipra-bridge/reduced-model-descent-prototype'
PARENT = BASE / 'reviews/ordinary12-model-square-divisor-independent-audit'
OUT = Path('/tmp/ipra-reduced-model-descent-pair-01')
PAIR = Path('/tmp/ipra-ordinary12-coexistence-pair-01')
SQUARE = Path('/tmp/ipra-model-square-divisor-replay-46be-02')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT = '2a3e44b6579798dd99557fcb050776fef12678479b24528b1f767b513e594742'
SOURCE = 'd50d9a57f8529046c6492604683fa6e29eab8cfa74ec5fb7a11ce6685e6bd96d'
SEED = '5c745c178aa64429340e217eb0ef3e2bffba98e747f7c0a29ff3c1ca25c95f97'
OBJECT = '1a7e42a08cc3ae1de1d9162ef2af94855b7cc86ebe8c98551fb384883f0a8a9b'
LOG = '4b733340884b98a0623b3714eae788490b7cec8535593a52dfd76d029f4ec051'
PARENT_RECEIPT = '513cbf379c6fcae6ff63d0da4d8d2db5fe3f23e2d2615986f71a03cd32392623'
REPORTS = ('ring_bounds', 'model_bounds', 'bez_iff_diff', 'ring_transform_norm',
           'ring_transform_interval', 'ring_transform_bezout', 'model_signed_numerator')

def need(ok, why):
    if not ok:
        raise ValueError(why)

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'README.md', PKG/'replay.py', PKG/'ReducedNormBounds.lean',
              *(PKG/'evidence'/name for name in ('receipt.json', 'terminal.json', 'author.log', 'peer.log')),
              *(PKG/'observations'/name for name in ('attempt01-terminal.json','attempt01.lean','attempt02-terminal.json','attempt02.lean','initial-failures.json'))]:
        b = subprocess.run(['git','show','c8ded28bc6:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+str(p))
    obs = json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==18589 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT and
         obs['optimized_mode_control_exit']==1,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r = json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_REDUCED_MODEL_DESCENT_STEP' and r['parent_comparison']['status']=='MATCHED_PASS' and
         r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for p,h in r['pins'].items():need(sha(p)==h,'fixed input '+p)
    need(sha(PARENT/'CHECK.json')==PARENT_RECEIPT,'audit pin')
    # The earlier audit's broad git-diff guard now rejects a subsequent README
    # update; retain that result and separately bind the mathematical source.
    pr = subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(pr.returncode==1 and b'historical suffix packet drift' in pr.stderr,'parent rerun drift guard')
    square_pkg=BASE/'research/ordinary12-ipra-bridge/model-square-divisor-prototype'
    drift=subprocess.run(['git','diff','--name-only','bd56831045','--',str(square_pkg.relative_to(ROOT))],cwd=ROOT,check=True,capture_output=True,text=True).stdout.splitlines()
    need(drift==[str((square_pkg/'README.md').relative_to(ROOT))],'parent drift limited to README')
    source=square_pkg/'ModelSquareDivisor.lean'
    historical=subprocess.run(['git','show','bd56831045:'+str(source.relative_to(ROOT))],cwd=ROOT,check=True,capture_output=True).stdout
    need(hashlib.sha256(historical).hexdigest()==sha(source)=='34fcc00c00408871b5bd98d6ebbff3a3d03bb68f56410d2441c3e056c2d0a2c6','parent source pin')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PAIR/side/'child-output/lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        need(sha(run/'src/DiophantineConsistency/ReducedNormBounds.lean')==sha(PKG/'ReducedNormBounds.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(run/'ReducedNormBounds.olean')==row['object_sha256']==OBJECT,'object')
        need(not (proj/'ModelSquareDivisor.olean').is_symlink() and sha(proj/'ModelSquareDivisor.olean')==sha(SQUARE/side/'ModelSquareDivisor.olean')==row['seed_sha256']==SEED,'seed')
        parentfiles={p.name for p in prior.glob('*.olean')}
        links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==64 and links==parentfiles,'parent coverage')
        for name in links:
            p=proj/name;target=prior/name
            need(p.resolve()==target.resolve() and sha(p)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PAIR/side/'child-output/lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            p=bb/name;target=priorbb/name
            need(p.is_symlink() and p.resolve()==target.resolve() and sha(p)==sha(target),'BusyBeaver link')
        deps={str(PACKAGE/'Init.olean'),str(PACKAGE/'Mathlib/Tactic/Linarith.olean'),str(proj/'ModelDifferenceRing.olean'),str(proj/'ModelSquareDivisor.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(run/'ReducedNormBounds.olean'),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'compiler log')
        reports=re.findall(r"^'ReducedNormBounds\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need(tuple(n for n,_ in reports)==REPORTS and [a for _,a in reports]==row['axiom_reports'] and
             all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in reports) and
             not re.search(r'warning:|sorryAx|\bsorry\b|error:',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':len(links),'seed_sha256':SEED,'object_sha256':OBJECT,
                          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    # Small standard-integer checks supplement, and do not prove, the model lemmas.
    count=0
    for r0 in range(1,21):
      for b in range(1,6):
       for v in range(2,101):
        n=(r0+1)*(v*b)**2-b*b
        if n%r0:continue
        a=isqrt(n//r0)
        if a*a!=n//r0 or gcd(a,b)!=1:continue
        need(r0%(b*b)==0,'finite divisor')
        s=r0//(b*b);vp=(2*r0+1)*v-2*b*s*a;ap=(2*r0+1)*a-2*(r0+1)*v*b
        need(v*b<a and r0*a<(r0+1)*v*b and -v<vp<v and
             (r0+1)*vp*vp*b*b-r0*ap*ap-b*b==0 and gcd(abs(ap),b)==1,'finite transformed state')
        count+=1
    need(count>0,'nonempty sample')
    print(json.dumps({'status':'PASS_INDEPENDENT_REDUCED_MODEL_DESCENT_AUDIT','source_commit':'c8ded28bc6',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':18589,'recorded_outer_exit':0,
      'parent_audit_sha256':PARENT_RECEIPT,'parent_audit_rerun_exit':1,
      'parent_audit_rerun_reason':'historical packet drift: subsequent README edit only; source independently matched to historical commit','runs':summaries,
      'finite_bounds':'1 <= r <= 20, 1 <= b <= 5, 2 <= v <= 100, exact square a and gcd(a,b)=1',
      'finite_valid_states':count,'scope':'Read-only artifact audit and bounded sanity checks; no Lean rerun, transformed nonzero, termination, graph binding or object-level iPRA proof.'},indent=2))

if __name__=='__main__':main()
