#!/usr/bin/env python3
"""Exact-domain boundary regressions. Explicit checks also run under python -O.
Expected schema hashes were computed from the frozen delivered archive; schema
contents and legal dynamics must remain unchanged by the input-validation fix.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, json, sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from build_net import fire, initial
from source_quadratic import semantic_table
from peak_quadratic import compile_peak
EXPECTED_SCHEMAS = {'1,False,False': 'bfb96e7f10500094519df568e9eed81ba971906c1f8b6f22b3cb9a3e35691956', '1,True,False': '7ef6218fef75c091096e7dba0dfd64c8aad4b11f0356c425233bdf0e3944d58a', '1,True,True': 'f6454b4d63e51a95973a9dfae85c99ef92b5060a69c7b2e7226e83ce20c37275', '2,False,False': 'c0c65db00a4f70e725b498b7da57bb31019cfa280d3b74d01825710ba0cb7332', '2,True,False': '3fbc448f893058b29f46a41acdafc62b342d972bdfa0e6c890107ee932deb48b', '2,True,True': '6c66ec32a6ae181ba9c976b2e34677a7738aa47308a5e2c067eec1bbbaed036c', '3,False,False': 'bd399a31a9c3b3143d57f3629c36d56cc6c0f9d8f316035724a6890975e37725', '3,True,False': '24135d2c678318a9999252ec2ff019569c1dd6d7a596307e740fb10cfacb15e4', '3,True,True': '31dd44a28da80d1e2f9856f2288b53712b86f41a5dd825c01e1d3904631a1f1f'}

def require(condition, message):
    if not condition: raise AssertionError(message)

rejections=0

def rejects(call, label):
    global rejections
    try: call()
    except ValueError: rejections+=1
    else: raise AssertionError('Accepted malformed call: '+label)

net=json.loads((ROOT/'reset_net.json').read_text())
table=semantic_table(json.loads((ROOT/'source/virtual3.json').read_text()))
finish=next(t for t in net['transitions'] if t['name']=='finish')
for value in [0,1,0.0,0.5,1.0,None,'','yes',[],{},Fraction(1,2)]:
    rejects(lambda value=value:compile_peak(table,1,with_duration=value),'with_duration '+repr(value))
    rejects(lambda value=value:compile_peak(table,1,all_durations=value),'all_durations '+repr(value))
rejects(lambda:compile_peak(table,1,with_duration=False,all_durations=True),'incompatible Boolean options')
for value in [-1,True,False,0.0,1.0,Fraction(1,1),'1',None]:
    rejects(lambda value=value:initial(net,value,0),'initial L '+repr(value))
    rejects(lambda value=value:initial(net,0,value),'initial R '+repr(value))
for marking in [None,[],[('q:DRAIN',1)],{'q:DRAIN':1,'ghost':999}, {'q:DRAIN':1,'ghost':0}, {1:0,'q:DRAIN':1}]:
    rejects(lambda marking=marking:fire(net,marking,finish),'marking '+repr(marking))
for value in [-1,True,False,0.0,1.0,0.5,Fraction(1,1),'1',None]:
    for place in ['q:DRAIN','L']:
        marking={'q:DRAIN':1,place:value}
        rejects(lambda marking=marking:fire(net,marking,finish),'marking coordinate '+repr(marking))
rejects(lambda:fire(net,{},finish),'disabled finish')
require(initial(net,0,0)=={'L':0,'R':0,'budget':0,'q:START':1},'valid zero initial')
require(initial(net,10**100,2)['budget']==10**100+2,'large exact initial')
require(fire(net,{'q:DRAIN':1,'L':0},finish)==({'q:DONE':1},0),'valid finish')
for h in (1,2,3):
    for wd,ad in [(False,False),(True,False),(True,True)]:
        packet=compile_peak(table,h,with_duration=wd,all_durations=ad)
        digest=hashlib.sha256(json.dumps(packet,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        require(digest==EXPECTED_SCHEMAS[f'{h},{wd},{ad}'],'full schema changed')
        count=packet['variables']['count']
        coords=[i for terms in packet['linear_forms'].values() for i,c in terms]
        affines=[x['affine'] for x in packet['affine_squares']]+[x[k] for x in packet['quadratic_products'] for k in ['left','right']]
        coords.extend(i for a in affines for i,c in a['variables'])
        require(all(type(i) is int and 0<=i<count for i in coords),'dangling coordinate')
trace=json.loads((ROOT/'accepting_reset_trace.json').read_text())['trace']
for row in trace:
    old=dict(row['old'])
    result=fire(net,old,row['transition'])
    require(result==(row['new'],row['reset_loss']),'legal trace changed')
    require(old==row['old'],'input marking mutated')
weighted_cases=0
for pre in range(3):
    for post in range(3):
        for reset in [False,True]:
            for old in range(pre,5):
                toy={'places':['x'],'transitions':[{'name':'weighted','pre':{'x':pre},'post':{'x':post},'reset':['x'] if reset else []}]}
                out,loss=fire(toy,{'x':old},0)
                require(out.get('x',0)==(0 if reset else old-pre)+post,'weighted reset/output order')
                require(loss==(old-pre if reset else 0),'weighted reset loss')
                weighted_cases+=1
print(json.dumps({'status':'PASS','optimization':sys.flags.optimize,'rejected_calls':rejections,'invalid_input_or_option_calls':rejections-1,'disabled_transition_calls':1,'full_schema_hash_matches':len(EXPECTED_SCHEMAS),'valid_stored_firings':len(trace),'weighted_overlap_cases':weighted_cases},sort_keys=True))
