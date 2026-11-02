#!/usr/bin/env python3
"""Read-only audit of both model negative-residue suffix chains."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-negative-residue'
PARENT=BASE/'reviews/ordinary12-coexistence-pair-independent-audit'
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-03')
OUT=Path('/tmp/ipra-thirteen-negative-residue-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='a7ce2e650644acd4ea0a875c86fd04d2dcbf98f2950394822f32092e4c20fcab'
PARENT_RECEIPT='5f1fc7a6f519088588ed568e3266da6d109490d556d459a7949d257cbb1bc11d'
SRC={'DiscreteOrderedRingFacts':'3870325628b4148b2825e1af96bbec91ecbb115e2e57a83d580df97ea53f07aa',
     'ArithmeticNegativeNorms':'00c0a3b6bbddd9d6ea23d1e1ecbcc2e02f383a76e7618f6328288d413719d7ef',
     'ModelArithmetic':'2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6',
     'ArithmeticOddOrdinateResidue':'cb4080289e247320fe8f5930c471ceb02c5ad01fc6cb73cbdd813468ade7fa7c',
     'ModelBNegativeResidue':'13f370a5127ca9a9b53a127f05d5196b27c645cfc127710128487d48e9c45476'}
OBJ={'DiscreteOrderedRingFacts':'b6b6217f15586efe7f0fec4d2c94e3824e995ae40515d08550968f89b4888dd7',
     'ArithmeticNegativeNorms':'33cf47041c950f77cd4535d629dcddfa27ff9ea1fcd21cc1af0fb732dd5eb319',
     'ModelArithmetic':'252db63f2ec2494b7c7c25744c6aed5a28ae0b353004f0d197cab7559f82644b',
     'ArithmeticOddOrdinateResidue':'5203c8deec8ad4a43f824b2c13c7cf555fc2dd37779b4bb27cfba78f239ded02',
     'ModelBNegativeResidue':'b6d67e3b70cf7cbecfcf59ed57f6c88a2e7bfc61ee93f264a4a523fbe6284f9a'}


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def coord(a,t):
    x,y=1,0;d=(a+1)*(a+3)
    for _ in range(t):x,y=(a+2)*x+d*y,x+(a+2)*y
    return x,y


def main():
    for name,h in SRC.items():
        path=PKG/(name+'.lean') if name=='ModelBNegativeResidue' else BASE/'Lean/DiophantineConsistency'/(name+'.lean')
        data=subprocess.run(['git','show','9d08926d17:'+path.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(data).hexdigest()==digest(path)==h,'source pin '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(obs['session_id']==66854 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_NEGATIVE_RESIDUE '+RECEIPT and
         digest(PKG/'replay-receipt.json')==digest(OUT/'receipt.json')==RECEIPT,'wrapper observation')
    need(r['status']=='PASS_PAIRED_THIRTEEN_NEGATIVE_RESIDUE' and len(r['runs'])==2 and r['parent_comparison']['status']=='MATCHED_PASS','pair status')
    parent=json.loads((PARENT/'CHECK.json').read_bytes());pt=json.loads((PARENT/'terminal-observation.json').read_bytes())
    need(digest(PARENT/'CHECK.json')==PARENT_RECEIPT and pt['audit_observed_exit_code']==0 and pt['receipt_sha256']==PARENT_RECEIPT and
         parent['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT','audited parent')
    for path,h in r['fixed_inputs_sha256'].items():need(digest(path)==h,'fixed input '+path)
    manifest=json.loads((SNAP/'manifest.json').read_bytes());parentmods=set(manifest['order']);need(len(parentmods)==70,'parent count')
    need('DiophantineConsistency.ArithmeticOddOrdinateResidue' not in parentmods,'later module misclassified as parent')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        need(row['label']==side and len(row['modules'])==5,'side modules')
        run=OUT/side;project=run/'lib/DiophantineConsistency';prior=PAIR/side/'child-output/lib/DiophantineConsistency'
        links=row['parent_links_sha256'];need(len(links)==64 and set(links)=={str(project/p.name) for p in prior.glob('*.olean')},'parent link coverage')
        for link,h in links.items():
            q=Path(link);need(q.is_symlink() and q.resolve()==(prior/q.name).resolve() and digest(q)==h,'parent link '+link)
        need((run/'lib/BusyBeaver').is_symlink() and (run/'lib/BusyBeaver').resolve()==(PAIR/side/'child-output/lib/BusyBeaver').resolve(),'BusyBeaver parent link')
        available=set(parentmods);warnings=0
        for item,name in zip(row['modules'],SRC):
            src=run/'src/DiophantineConsistency'/(name+'.lean');obj=project/(name+'.olean')
            need(item['name']==name and item['exit']==item['deps_exit']==0 and not item['stderr'],'child exits '+side+' '+name)
            need(digest(src)==item['source_sha256']==SRC[name] and not obj.is_symlink() and digest(obj)==item['object_sha256']==OBJ[name],'source/object '+name)
            need(item['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and item['command'][-1]==str(obj),'bounded command '+name)
            imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);deps={str(PACKAGE/'Init.olean')}
            for dep in imports:
                path=(run/'lib' if dep.startswith(('DiophantineConsistency.','BusyBeaver.')) else PACKAGE)/Path(*dep.split('.')).with_suffix('.olean')
                if dep.startswith(('DiophantineConsistency.','BusyBeaver.')):need(dep in available,'direct import order '+dep)
                need(path.is_file(),'dependency exists '+dep);deps.add(str(path))
            need(set(item['deps_stdout'].splitlines())==deps,'exact direct deps '+name)
            lines=[line.split('warning:',1)[1].strip() for line in item['stdout'].splitlines() if 'warning:' in line]
            need(all(x=='`push_neg` has been deprecated. Prefer using `push Not` instead.' for x in lines),'unexpected warning '+name)
            warnings+=len(lines);need(not re.search(r'\b(?:sorryAx|sorry|admit|admitted)\b|^.*error:',item['stdout'],re.M),'error or admission '+name)
            if name=='ModelBNegativeResidue':
                need(not lines and item['stdout']=="'ModelBNegativeResidue.ordinate_plus_one_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and
                     item['axiom_reports']==['propext, Classical.choice, Quot.sound'],'final axiom report')
            available.add('DiophantineConsistency.'+name)
        need(warnings==6,'warning count '+side)
        summaries.append({'side':side,'parent_links':len(links),'objects':[OBJ[x] for x in SRC],
                          'recorded_compiler_exits':[0]*5,'recorded_dependency_exits':[0]*5,'push_neg_deprecation_warnings':warnings})
    samples=0
    for I in range(2,13):
      for b in range(1,I+1):
       if I%b:continue
       for R in (3,7,11):
        y=coord(I-2,R)[1];need((y+1)%(4*b)==0,'finite residue case');samples+=1
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_NEGATIVE_RESIDUE_AUDIT','source_commit':'9d08926d17',
      'recorded_outer_exit':obs['outer_exit_code'],'recorded_outer_session':obs['session_id'],'author_receipt_sha256':RECEIPT,
      'parent_audit_sha256':PARENT_RECEIPT,'runs':summaries,'finite_residue_cases':samples,
      'scope':'Read-only paired suffix artifact audit and finite standard examples; no Lean rerun, signed carrier, fixed-port calibration, 69-op converse or iPRA theorem.'},indent=2))


if __name__=='__main__':main()
