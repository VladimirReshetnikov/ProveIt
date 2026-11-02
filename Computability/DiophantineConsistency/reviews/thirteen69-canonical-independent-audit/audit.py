#!/usr/bin/env python3
"""Read-only audit of both canonical expression compilation chains."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen69-canonical-binding'
OUT=Path('/tmp/ipra-thirteen69-canonical-pair-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='c911357506f64cf71477a925c19b5c74c8fca4feabf1a0b7af57d20206ebce1a'
NAMES=('ShortEquation','ThirteenCarrier','Thirteen69Canonical')
SRCS=('2d447a166a33dedb90c8acdf0755d584a9d057bf46a047e0a454bf150f628b68','2f19e9690841d15d48a281cfafd8813270e0dcfe38a9f6c68ab9d2f9d85453ca','dd95d8575ef65cfd425f869176e870d277a43e53b778bf153f8f85545fa2e02d')
OBJS=('6aaa12eec5f197a5fe816c33982c3fb48de96ecdf76f4374ea4da34197885ffd','54da7156e0795e6c91b225c12bd2f0965a3cad69752e6f0fa8eeb52337c2733e','f70d33e889977227619bd5f0845b527f3c14723298b048cdb1603dbd03f74b50')

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [*(PKG/x for x in ('README.md','replay.py','Thirteen69Canonical.lean','replay-receipt.json','terminal-observation.json')),
              *(PKG/'observations'/x for x in ('failed-attempts.md','expand-full-ring.lean','expand-ac-simp.lean')),
              *(BASE/'Lean/DiophantineConsistency'/(x+'.lean') for x in NAMES[:2])]:
        blob=subprocess.run(['git','show','8d0f2795e6:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'commit bytes '+str(p))
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==81960 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN69_CANONICAL '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN69_CANONICAL' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    comparator=BASE/'research/fresh-project-closure/compare.py'
    p=subprocess.run([sys.executable,'-I','-S',str(comparator),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')],capture_output=True,timeout=120)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==r['parent_comparison'],'parent comparator')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PAIR/side/'child-output/lib/DiophantineConsistency'
        links=row['parent_links_sha256'];need(row['label']==side and len(links)==64 and set(links)=={str(proj/p.name) for p in prior.glob('*.olean')},'parent coverage')
        for link,h in links.items():
            q=Path(link);need(q.is_symlink() and q.resolve()==(prior/q.name).resolve() and sha(q)==h,'link '+link)
        bb=run/'lib/BusyBeaver';need(bb.is_symlink() and bb.resolve()==(PAIR/side/'child-output/lib/BusyBeaver').resolve(),'BusyBeaver')
        need(len(row['modules'])==3,'module count')
        for i,(item,name) in enumerate(zip(row['modules'],NAMES)):
            src=run/'src/DiophantineConsistency'/(name+'.lean');obj=proj/(name+'.olean')
            need(item['name']==name and item['exit']==item['deps_exit']==0 and not item['stderr'],'child exits')
            need(sha(src)==item['source_sha256']==SRCS[i] and not obj.is_symlink() and sha(obj)==item['object_sha256']==OBJS[i],'source/object '+name)
            need(item['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and item['command'][-1]==str(obj),'command')
            imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);deps={str(PACKAGE/'Init.olean')}
            for dep in imports:
                target=(run/'lib' if dep.startswith(('DiophantineConsistency.','BusyBeaver.')) else PACKAGE)/Path(*dep.split('.')).with_suffix('.olean')
                need(target.is_file(),'dependency '+dep);deps.add(str(target))
            need(set(item['deps_stdout'].splitlines())==deps,'direct dependencies '+name)
            need(not re.search(r'warning:|error:|sorryAx|\bsorry\b',item['stdout']),'warnings or admissions')
            if i<2:need(item['stdout']=='' and item['axiom_reports']==[],'dependency output')
            else:
                reports=re.findall(r"^'Thirteen69Canonical\.([^']+)' depends on axioms: \[([^\]]*)\]$",item['stdout'],re.M)
                need([n for n,_ in reports]==['eval_literal','internal_zero','shifted_zero','current_zero'] and
                     [a for _,a in reports]==['propext']+['propext, Classical.choice, Quot.sound']*3 and
                     item['axiom_reports']==[a for _,a in reports],'axiom reports')
        summaries.append({'side':side,'parent_links':64,'recorded_compiler_exits':[0]*3,'recorded_dependency_exits':[0]*3,'object_hashes':list(OBJS)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN69_CANONICAL_AUDIT','source_commit':'8d0f2795e6',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':81960,'recorded_outer_exit':0,
      'parent_comparator_rerun_exit':0,'runs':summaries,
      'scope':'Read-only suffix audit; no Lean rerun, exact JSON graph binding, 69-operation count, all-model converse, fixed-port calibration, or iPRA proof.'},indent=2))

if __name__=='__main__':main()
