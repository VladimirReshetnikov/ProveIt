#!/usr/bin/env python3
"""Check the symbolic calibration transformation and recorded artifacts."""
from hashlib import sha256
from pathlib import Path
import json
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
DC=Path(__file__).resolve().parents[2]
BR=DC/'research/ordinary12-ipra-bridge'
base=BR/'compact44-symbolic-rank-calibration-prototype'
old=BR/'compact44-controller-choice-prototype/ArithmeticControllerChoiceCompact44.lean'
new=base/'ArithmeticControllerChoiceCompact44Triangle.lean'
triangle=base/'CompactControllerTriangle.lean'
cantor=DC.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean'
unit=BR/'compact44-controller-abstract-bridge-prototype/observations/terminal.json'
tmp=Path('/tmp/ipra-compact44-symbolic-unit-join')
pins={base/'observations/terminal.json':'fb41a5bcbabf86a0f0717d4511411f9a45f4937cf53b9d07fac27521da3fbbcf',
      base/'run.py':'222ff6c71d24843734337de36418045db8f8e96a3daf0eaac79825c395542641',
      base/'check_extraction.py':'953ba44eebb47ee59217bb984fe2bb827a7f93d006e5a7e24fddd17eb4e5a297',
      old:'27d550683bcbeb285d3b84b621a2e4f61f691460ababca6c777e3214c2f9cc8e',
      new:'ef4a314368a8387b1ba74fa6de1799e42ae96f0734662dc956c293870597fff1',
      triangle:'fec82b8a513f2133255a7f5f5d9bdd7be23ab40ef52eeb30f7c95c96ea034b88',
      cantor:'aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84',
      unit:'4cd2940b74cb1b74a711aacac1f1dad1f02a0cbc783e24260697574cad07c595'}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def check_pins():
    for p,h in pins.items(): need(sha(p)==h,'changed input: '+str(p))
check_pins()

# Reconstruct the complete adapted controller text independently of the
# companion checker; the whole file, not just selected lemmas, must match.
s=old.read_text().replace('import BusyBeaver.ZFC.ArithmeticCantor',
                          'import DiophantineConsistency.CompactControllerTriangle')
s=s.replace('namespace DiophantineConsistency.ArithmeticControllerChoiceCompact44',
            'namespace DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle')
s=s.replace('end DiophantineConsistency.ArithmeticControllerChoiceCompact44',
            'end DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle')
s=s.replace('  SetTheory.BusyBeaver.ZFC.ArithmeticCantor','  CompactControllerTriangle')
s=s.replace('DiophantineConsistency.ArithmeticControllerChoiceCompact44.',
            'DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle.')
need(s==new.read_text(),'full transformed controller source')
a,b=cantor.read_text(),triangle.read_text()
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]' in a and
     'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]' in b,'triangle model context')
for start, enda, endb in [('def triangle (s : V)','lemma triangle_double','lemma triangle_double'),
                          ('lemma triangle_double','lemma triangle_succ','lemma triangle_succ'),
                          ('lemma triangle_succ','lemma triangle_mono','lemma le_triangle'),
                          ('lemma le_triangle','noncomputable def cantor','#print axioms triangle_succ')]:
    aa=a[a.index(start):a.index(enda,a.index(start))].strip()
    bb=b[b.index(start):b.index(endb,b.index(start))].strip()
    need(aa==bb,'triangle declaration: '+start)

record=json.loads((base/'observations/terminal.json').read_text())
prior=json.loads(unit.read_text())['stages']
need(len(prior)==4 and all(x['exit_code']==0 for x in prior),'unit stages')
need(record['unit_objects']==[x['object_sha256'] for x in prior],'unit object inventory')
for x in prior: need(sha(tmp/'lib'/(x['module']+'.olean'))==x['object_sha256'],'unit object')
expected=('DiophantineConsistency/CompactControllerTriangle',
          'DiophantineConsistency/ArithmeticControllerChoiceCompact44Triangle',
          'AliasRankCalibration','ActualRankCalibration')
stages=record['stages']
need([x['module'] for x in stages]==list(expected),'stage inventory')
for stage in stages:
    module=stage['module'];name=module.split('/')[-1]
    need(stage['exit_code']==0 and not stage['sorry_present'],'compiler status: '+name)
    need(sha(base/(name+'.lean'))==stage['source_sha256']==sha(tmp/'src'/(module+'.lean')),
         'source snapshot: '+name)
    need(sha(base/'observations'/(name+'.log'))==stage['log_sha256'] and
         sha(tmp/'lib'/(module+'.olean'))==stage['object_sha256'],'log/object: '+name)
    log=(base/'observations'/(name+'.log')).read_text()
    need('sorryAx' not in log and 'error:' not in log,'bad log: '+name)
    if name=='ArithmeticControllerChoiceCompact44Triangle':
        need(log.count('warning:')==2 and 'unused in theorem' in log and
             'Variable name `hw`' in log and stage['warning_present'],'controller warnings')
    else: need('warning:' not in log and not stage['warning_present'],'unexpected warning: '+name)
    need((base/'observations'/(name+'.deps.stderr')).read_bytes()==b'','dependency stderr: '+name)
last=(base/'observations/ActualRankCalibration.log').read_text()
reports=re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]",last,re.M|re.S)
need(len(reports)==1 and reports[0][0]=='CompactActualRankCalibration.symbolic_rank_calibration' and
     {x.strip() for x in reports[0][1].split(',')}=={'propext','Classical.choice','Quot.sound'},
     'final axiom report')
check_pins()
for stage in stages:
    need(sha(tmp/'lib'/(stage['module']+'.olean'))==stage['object_sha256'],'object drift after check')
print(json.dumps({'status':'PASS_RANK_CALIBRATION_SOURCE_ARTIFACT_REVIEW',
                  'stages':len(stages),'unit_objects':len(prior),'controller_warnings':2,
                  'scope':'source transformation and point-in-time artifacts; no Lean replay or closure audit'},sort_keys=True))
