#!/usr/bin/env python3
"""Inspect pinned conditional-rank sources and author artifacts; no Lean run."""
from hashlib import sha256
from pathlib import Path
import json
import sys
if not __debug__ or sys.flags.optimize: raise RuntimeError('optimized Python is rejected')
DC=Path(__file__).resolve().parents[2]
BR=DC/'research/ordinary12-ipra-bridge'
base=BR/'compact44-controller-realizable-bridge-prototype'
tmp=Path('/tmp/ipra-compact44-symbolic-unit-join')
pins={base/'ChosenRankIfRealizable.lean':'8fb8d8ce889320a7fead10161d5f5b65db7bfd41079a2abbb93bd6439b572236',
      base/'observations/terminal.json':'72db65bc232ac94769b6050a95106b2cb023ee827c9571faa85c6c9d7961d061',
      base/'observations/compile.log':'647abee2249821e61d70524cf3ce5d52bcc6f06e50837a76c4e35bc37fb73a9d',
      base/'observations/deps':'1d28231536fdbac02469948b8ccd76dc0a18404565e12c717c12df66ae683812',
      BR/'compact44-chosen-controller-calibration-prototype/ChosenControllerCalibration.lean':
          '8756138da643303e6dd05726fc6bd6c630165f810418e955e51f9cb1eeab8e28',
      BR/'compact44-conditional-rank-variation-prototype/CompactRankVariation.lean':
          'ce394f442d6074632299ae3e6b8564f5b123eedf5625ec076b80ac1ca7e02404',
      DC/'Lean/DiophantineConsistency/ArithmeticPacking.lean':
          '3cb27eae0e99b3ab11c76d0e1b279d2b4652d4d662944719e213f81235fbb2f1',
      tmp/'src/ChosenRankIfRealizable.lean':'8fb8d8ce889320a7fead10161d5f5b65db7bfd41079a2abbb93bd6439b572236',
      tmp/'src/CompactRankVariationRetry.lean':'ce394f442d6074632299ae3e6b8564f5b123eedf5625ec076b80ac1ca7e02404',
      tmp/'lib/ChosenControllerCalibration.olean':'695ee1a87daed84161d0f00ee879739032fe9e2a5b18a6a9c5238554b4dcebe6',
      tmp/'lib/CompactRankVariationRetry.olean':'4a83f057ab047dd1c8f16c0b716327c8a52ae2f4a2c92dac386e1a6ccc599f00',
      tmp/'lib/ChosenRankIfRealizable.olean':'7dc2ce677e43824bb7c404512e12c84d51f42cabe6b927dd8ca7e2d332bf5eb6'}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def check():
    for p,h in pins.items(): need(sha256(p.read_bytes()).hexdigest()==h,'hash drift: '+str(p))
check();receipt=json.loads((base/'observations/terminal.json').read_text())
need(receipt['exit_code']==0 and not receipt['warning_present'] and not receipt['sorry_present'] and
     receipt['source_sha256']==pins[base/'ChosenRankIfRealizable.lean'] and
     receipt['object_sha256']==pins[tmp/'lib/ChosenRankIfRealizable.olean'],'compile receipt')
need(receipt['inputs']=={'ChosenControllerCalibration':pins[tmp/'lib/ChosenControllerCalibration.olean'],
                         'CompactRankVariationRetry':pins[tmp/'lib/CompactRankVariationRetry.olean']},
     'direct input hashes')
log=(base/'observations/compile.log').read_text().strip()
need(log=="'CompactChosenRankIfRealizable.chosen_rank_if_realizable' depends on axioms: [propext, Classical.choice, Quot.sound]",'axiom report')
need((base/'observations/deps.stderr').read_bytes()==b'','dependency stderr')
deps=(base/'observations/deps').read_text().splitlines()
need(set(deps)=={str(tmp/'lib/ChosenControllerCalibration.olean'),str(tmp/'lib/CompactRankVariationRetry.olean'),
                 '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean'} and len(deps)==4,'direct deps')
check()
print(json.dumps({'status':'PASS_CONDITIONAL_REALIZATION_SOURCE_REVIEW','direct_inputs':2,
                  'scope':'point-in-time source/artifact inspection; no Lean replay or full closure audit'},sort_keys=True))
