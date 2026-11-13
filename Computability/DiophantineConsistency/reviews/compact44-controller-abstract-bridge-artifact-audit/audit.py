#!/usr/bin/env python3
"""Point-in-time checks of the four-stage author bridge; no Lean execution."""
from hashlib import sha256
from pathlib import Path
import json
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
DC=Path(__file__).resolve().parents[2]
base=DC/'research/ordinary12-ipra-bridge/compact44-controller-abstract-bridge-prototype'
obs=base/'observations'
prior=base.parent/'compact44-symbolic-controller-join-prototype/observations/terminal.json'
alias=base.parent/'compact44-symbolic-controller-alias-prototype/observations03/terminal.json'
tmp=Path('/tmp/ipra-compact44-symbolic-unit-join')
init=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean')
pins={obs/'terminal.json':'4cd2940b74cb1b74a711aacac1f1dad1f02a0cbc783e24260697574cad07c595',
      base/'run.py':'694ec36feb0042f45b9d4c1198c412420beb55e144dbd4c0accf7533cf773a13',
      prior:'78fc1356e297f5967017ae5b4531dc0deb9b00deff906cadbbb99453bbb70850',
      alias:'5212c10fe67203a9f8da72fb5ad687d15dc1b3251d7d3bc84aaf2463cc5e39ab',
      init:'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
names=('AliasResidueNumeral','AliasUnitGivenResidue','AliasUnitDischarged','ActualUnitTransport')
theorems=('CompactAliasResidueNumeral.alias_residue_numeral',
          'CompactAliasUnitGivenResidue.alias_unit_given_residue',
          'CompactAliasUnitDischarged.alias_unit','CompactActualUnitTransport.actual_unit')
deps=(('KernelAliasExplicit',),('DiophantineConsistency/ArithmeticConstructionUnitCompact44','KernelAliasExplicit'),
      ('AliasUnitGivenResidue','AliasResidueNumeral'),('AliasUnitDischarged',))
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(path): return sha256(Path(path).read_bytes()).hexdigest()
def check_pins():
    for path,pin in pins.items(): need(sha(path)==pin,'receipt/runner/init drift: '+str(path))
check_pins()
receipt=json.loads((obs/'terminal.json').read_text())
prior_records=json.loads(prior.read_text())['stages']
alias_record=json.loads(alias.read_text())['stages'][0]
need(len(prior_records)==5 and all(s['exit_code']==0 for s in prior_records[:4]),'prior stages')
need(receipt['earlier_stage_objects']==[s['object_sha256'] for s in prior_records[:4]],'prior object inventory')
for stage in prior_records[:4]:
    need(sha(tmp/'lib'/(stage['module']+'.olean'))==stage['object_sha256'],
         'prior object drift: '+stage['module'])
need(alias_record['exit_code']==0 and sha(tmp/'lib/KernelAliasExplicit.olean')==alias_record['object_sha256'],
     'alias object drift')
stages=receipt['stages']
need([s['module'] for s in stages]==list(names),'four-stage order')
for name,theorem,dependencies,stage in zip(names,theorems,deps,stages):
    need(stage['exit_code']==0 and not stage['warning_present'] and not stage['sorry_present'],
         'compiler stage: '+name)
    need(sha(base/(name+'.lean'))==stage['source_sha256']==sha(tmp/'src'/(name+'.lean')),
         'source snapshot: '+name)
    need(sha(obs/(name+'.log'))==stage['log_sha256'] and
         sha(tmp/'lib'/(name+'.olean'))==stage['object_sha256'], 'log/object: '+name)
    log=(obs/(name+'.log')).read_text()
    expected="'"+theorem+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
    need(log.strip()==expected and not any(x in log for x in ('sorryAx','error:','warning:')),
         'axiom report: '+name)
    need((obs/(name+'.deps.stderr')).read_bytes()==b'', 'dependency stderr: '+name)
    lines=(obs/(name+'.deps')).read_text().splitlines()
    expected_deps={str(init), *(str(tmp/'lib'/(item+'.olean')) for item in dependencies)}
    need(set(lines)==expected_deps and len(lines)==len(expected_deps)+1, 'direct dependency listing: '+name)
    need(all(Path(path).is_file() for path in lines), 'missing direct dependency: '+name)
    need(stage['command'][-1]==str(tmp/'lib'/(name+'.olean')) and
         stage['command'][-3]==str(tmp/'src'/(name+'.lean')), 'command paths: '+name)
check_pins()
for stage in prior_records[:4]:
    need(sha(tmp/'lib'/(stage['module']+'.olean'))==stage['object_sha256'],'prior drift after check')
for name,stage in zip(names,stages):
    need(sha(base/(name+'.lean'))==stage['source_sha256']==sha(tmp/'src'/(name+'.lean')) and
         sha(tmp/'lib'/(name+'.olean'))==stage['object_sha256'],'stage drift after check: '+name)
print(json.dumps({'status':'PASS_SYMBOLIC_CONTROLLER_BRIDGE_SOURCE_ARTIFACT_REVIEW',
                  'stages':len(stages),'prior_objects':4,'axiom_reports':4,
                  'scope':'point-in-time source/artifact checks; no Lean replay or closure audit'},sort_keys=True))
