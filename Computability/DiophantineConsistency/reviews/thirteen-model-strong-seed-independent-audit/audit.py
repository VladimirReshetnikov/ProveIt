#!/usr/bin/env python3
"""Read-only audit of the paired thirteen-variable model strong-seed suffix."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-strong-seed'
PARENT=BASE/'reviews/ordinary12-coexistence-pair-independent-audit'
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
OUT=Path('/tmp/ipra-thirteen-strong-seed-pair-01')
SRC='248a4601d87f7981a477cb55050b72624346d4ce4390966263f2e9b2c28e5b08'
PIGEON='ebdbc22e239754f8f686be6971742d1b02560c9ffa35d464d2aecc323370765c'
RECEIPT='9faa32f1c6715ffd6fd5a84330d46c545ad8c8aea3261c64c009144e841501f7'
PARENT_RECEIPT='5f1fc7a6f519088588ed568e3266da6d109490d556d459a7949d257cbb1bc11d'
OBJECTS={'ArithmeticPellPigeonhole':'c3eb02d03ffa9ab3b6f27cc09248a75fcca3c0ac33d6a18d3aa25d00abd944e1',
         'ModelBSeed':'eddeb048bd7ea3e514cdae77d6dfd07d8dc2247117b2b9e819683cd623cfbcc8'}


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    for path,h in ((PKG/'ModelBSeed.lean',SRC),(BASE/'Lean/DiophantineConsistency/ArithmeticPellPigeonhole.lean',PIGEON),
                   (PKG/'replay-receipt.json',RECEIPT)):
        data=subprocess.run(['git','show','e30959deed:'+path.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(data).hexdigest()==digest(path)==h,'historical file '+str(path))
    parent=json.loads((PARENT/'CHECK.json').read_bytes());pt=json.loads((PARENT/'terminal-observation.json').read_bytes())
    need(digest(PARENT/'CHECK.json')==PARENT_RECEIPT and pt['audit_observed_exit_code']==0 and pt['receipt_sha256']==PARENT_RECEIPT and
         parent['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT','independently audited parent')
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(obs['outer_exit_code']==0 and obs['session_id']==50440 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_STRONG_SEED '+RECEIPT and digest(OUT/'receipt.json')==RECEIPT,'observed wrapper exit')
    need(r['status']=='PASS_PAIRED_THIRTEEN_STRONG_SEED' and r['parent_comparison']['status']=='MATCHED_PASS' and
         r['parent_comparison']['rows']==70 and len(r['runs'])==2,'paired receipt')
    for path,h in r['fixed_inputs_sha256'].items():need(digest(path)==h,'fixed input '+path)
    warnings={};runs=[]
    for row,label in zip(r['runs'],('author','peer')):
        need(row['label']==label and len(row['modules'])==2,'sibling modules')
        run=OUT/label;project=run/'lib/DiophantineConsistency';parentlib=PAIR/label/'child-output/lib'
        links=row['parent_links_sha256'];need(len(links)==64,'parent link count')
        expected_links={str(project/p.name) for p in (parentlib/'DiophantineConsistency').glob('*.olean')}
        need(set(links)==expected_links,'complete parent project links')
        for link,h in links.items():
            q=Path(link);need(q.is_symlink() and q.resolve()==(parentlib/'DiophantineConsistency'/q.name).resolve() and digest(q)==h,'parent link '+link)
        need((run/'lib/BusyBeaver').is_symlink() and (run/'lib/BusyBeaver').resolve()==(parentlib/'BusyBeaver').resolve(),'BusyBeaver parent link')
        for m,name in zip(row['modules'],('ArithmeticPellPigeonhole','ModelBSeed')):
            src=run/'src/DiophantineConsistency'/(name+'.lean');obj=project/(name+'.olean')
            expected_src=PIGEON if name=='ArithmeticPellPigeonhole' else SRC
            need(m['name']==name and m['exit']==m['deps_exit']==0 and not m['stderr'], 'child exit '+label+' '+name)
            need(digest(src)==m['source_sha256']==expected_src and not obj.is_symlink() and digest(obj)==m['object_sha256']==OBJECTS[name], 'source/object '+name)
            need(m['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and m['command'][-1]==str(obj),'bounded compiler command')
            if name=='ArithmeticPellPigeonhole':
                deps={'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean',str(project/'ArithmeticPellRecurrence.olean'),
                      str(project/'ModelDifferenceRing.olean'),'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/LinearCombination.olean'}
                warning_lines=[line.split('warning:',1)[1].strip() for line in m['stdout'].splitlines() if 'warning:' in line]
                need(len(warning_lines)==3 and sum(x.startswith('`push_neg` has been deprecated.') for x in warning_lines)==2 and
                     sum(x.startswith("`mul_le_mul_left'` has been deprecated:") for x in warning_lines)==1,'pigeonhole warnings')
                warnings[label]=warning_lines
            else:
                deps={'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean',str(project/'ArithmeticPellPigeonhole.olean')}
                need(m['stdout']=="'ModelBSeed.strong_seed_with_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and
                     m['axiom_reports']==['propext, Classical.choice, Quot.sound'],'seed axiom report')
            need(set(m['deps_stdout'].splitlines())==deps,'direct imports '+name)
            need(not re.search(r'\b(?:sorryAx|sorry|admit|admitted)\b|^.*error:',m['stdout'],re.M),'error/admission '+name)
        runs.append({'side':label,'parent_project_links':len(links),'pigeon_object_sha256':OBJECTS['ArithmeticPellPigeonhole'],
                     'seed_object_sha256':OBJECTS['ModelBSeed'],'recorded_lean_exits':[0,0],'recorded_deps_exits':[0,0]})

    # Ordinary finite Pell examples supplement the arbitrary-model theorem.
    count=0;largest=0
    for a in range(5):
      for b in range(1,5):
       for c in range(1,5):
        N=b*c*c;x,y=1,0;delta=(a+1)*(a+3)
        for t in range(1,N*N+1):
            x,y=(a+2)*x+delta*y,x+(a+2)*y
            if y%N==0:break
        else:raise ValueError('finite seed search failed')
        i=y//N;need(t>0 and x>0 and i>0 and y==b*i*c*c and x*x==1+delta*y*y,'finite seed')
        count+=1;largest=max(largest,t)
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_MODEL_STRONG_SEED_AUDIT','reviewed_commit':'e30959deed',
       'author_receipt_sha256':RECEIPT,'recorded_outer_exit':0,'recorded_outer_session':50440,
       'parent_audit_receipt_sha256':PARENT_RECEIPT,'source_sha256':SRC,'pigeonhole_source_sha256':PIGEON,
       'runs':runs,'pigeonhole_deprecation_warnings_per_side':3,'warnings':warnings,
       'finite_cases':count,'finite_largest_t':largest,
       'scope':'Read-only audit of recorded paired suffix builds plus finite examples; no independent Lean replay, 69-op converse, fixed-port calibration or iPRA proof.'},indent=2))


if __name__=='__main__':main()
