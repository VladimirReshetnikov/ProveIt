#!/usr/bin/env python3
"""Independently enumerate the pinned square-only sign search."""
from pathlib import Path
from hashlib import sha256
import gzip
import json
import math
import random
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
BASE=REPO/'Computability/DiophantineConsistency/research/ordinary12-circuit-local-search/search.py'
SEARCH=REPO/'Computability/DiophantineConsistency/research/ordinary12-square-sign-search/search.py'
RECORDED=SEARCH.parent/'observations/search.json'
SUP=REPO/'Computability/DiophantineConsistency/con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
OUT=HERE/'observations'
P=1000000007
SEED=0x46BE
SOURCE_SHA='4472d0c6f9a7a6402e180978c3bf1d62e74e143177d078ea6ddd3d9d18806377'
BASE_SHA='98f54938a6eb1a158ffca98581dd5836300e13a6d07f9340ca52ab8ae55f3949'
OUT_SHA='f8652ff1e46813ff4c24fc372c037f390a6a9e3cbbb54c7726679afeb59c701e'
GRAPH_SHA='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
BINDING_SHA='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'
def h(b): return sha256(b).hexdigest()
def need(c,m):
    if not c: raise AssertionError(m)
need(not OUT.exists(),'output exists')
source,base,prior,graph_raw,binding_raw=(SEARCH.read_bytes(),BASE.read_bytes(),RECORDED.read_bytes(),
    (SUP/'circuits/positive12_95_degree70.json').read_bytes(),(SUP/'coefficients/BINDING.json').read_bytes())
for actual,pin,name in ((source,SOURCE_SHA,'search'),(base,BASE_SHA,'base'),(prior,OUT_SHA,'output'),
                        (graph_raw,GRAPH_SHA,'graph'),(binding_raw,BINDING_SHA,'binding')):
    need(h(actual)==pin,'pin drift: '+name)
need(P%4==3 and all(P%d for d in range(2,math.isqrt(P)+1)),'prime assumption')
graph=json.loads(graph_raw); binding=json.loads(binding_raw); expected=json.loads(prior)
rows=graph['source']; variables=graph['witnesses']+graph['fixed_numerals']
need(len(rows)==95 and len(set(variables))==16 and graph['output']=='P12','graph header')
payloads={}; fixed={}
for name in graph['fixed_numerals']:
    meta=binding['ports'][name]; data=(SUP/'coefficients'/meta['file']).read_bytes(); raw=gzip.decompress(data)
    need(h(data)==meta['sha256_gzip'] and h(raw)==meta['sha256_raw'] and len(raw)==meta['raw_bytes'],'payload: '+name)
    fixed[name]=int.from_bytes(raw,'little');payloads[name]=data

def live_count(data,out):
    definitions={r[0]:r for r in data}; seen=set()
    need(len(definitions)==len(data),'duplicate row')
    def visit(x):
        if x in definitions and x not in seen:
            seen.add(x);visit(definitions[x][2]);visit(definitions[x][3])
    visit(out)
    return len(seen)

def eligibility(data):
    # Independent scan counts appearances by operand position, not a set.
    definitions={row[0] for row in data}; uses={name:[] for name in definitions}
    for n,op,a,b in data:
        for x in (a,b):
            if x in uses: uses[x].append((n,op,a,b))
    return {name for name,cs in uses.items() if cs and all(op=='*' and a==name and b==name for _,op,a,b in cs)}

names=eligibility(rows)
need(names=={'Dstar','Z','f','polarA','vn'},'eligible set differs')
need(live_count(rows,'P12')==95,'graph is not fully live')
def exact_eval(data, inputs, flip=None):
    values={**inputs,**{n:n for n in range(5)}}
    for name,op,a,b in data:
        x,y=values[a],values[b]
        value=x+y if op=='+' else x-y if op=='-' else x*y
        values[name]=-value if name==flip else value
    return values['P12']

# Check the structural sign premise in independently evaluated integer DAGs.
rng=random.Random(314159)
exact_samples=0
for _ in range(7):
    inputs={name:rng.randint(-3,3) for name in variables}
    original=exact_eval(rows,inputs)
    for name in names:
        need(exact_eval(rows,inputs,name)==original,'square-use sign preservation: '+name)
        exact_samples+=1
# A node that also has an unsquared use is deliberately excluded.
unsafe=[['u','+','J',1],['u2','*','u','u'],['P12','+','u2','u']]
need('u' not in eligibility(unsafe),'non-square consumer accepted')
inputs={v:2 for v in variables}
need(exact_eval(unsafe,inputs)!=exact_eval(unsafe,inputs,'u'),'unsafe sign control failed')

def operate(op,x,y):
    return tuple((a+b)%P if op=='+' else (a-b)%P if op=='-' else (a*b)%P for a,b in zip(x,y))

def independent_direct(data, fixed_ports=None):
    """Enumerate each first gate and directly test second gates, no inversion/root pruning."""
    rng=random.Random(SEED)
    vals={v:tuple(rng.randrange(1,P) for _ in range(3)) for v in variables}
    if fixed_ports:
        vals.update({v:(n%P,)*3 for v,n in fixed_ports.items()})
    vals.update({n:(n,)*3 for n in range(5)})
    eligible=eligibility(data); original=live_count(data,'P12'); results=[]
    count_first=count_second=count_square=0
    for index,(name,op,left,right) in enumerate(data):
        original_value=operate(op,vals[left],vals[right])
        if name not in eligible:
            vals[name]=original_value;continue
        target=tuple(-x%P for x in original_value)
        need(all(target),'target has a zero sample')
        earlier=list(vals)
        need(all(all(vals[x]) for x in earlier if x!=0),'nonconstant operand has a zero sample')
        for i,a in enumerate(earlier):
            firsts=[(op1,b) for b in earlier[i:] for op1 in ('+','*')]
            firsts += [('-',b) for b in earlier]
            for op1,b in firsts:
                first=operate(op1,vals[a],vals[b]); count_first+=1
                if first==target:
                    replacement=data[:index]+[[name,op1,a,b]]+data[index+1:]
                    size=live_count(replacement,'P12')
                    if size<original:results.append({'target':name,'first':[op1,a,b],'live':size})
                for c in earlier:
                    cv=vals[c]
                    # Test actual second-gate outputs directly. The first
                    # component rejects almost all candidates cheaply.
                    for op2 in ('+','-','r-','*'):
                        count_second+=1
                        v0=((first[0]+cv[0])%P if op2=='+' else
                            (first[0]-cv[0])%P if op2=='-' else
                            (cv[0]-first[0])%P if op2=='r-' else first[0]*cv[0]%P)
                        if v0!=target[0]:continue
                        out=operate('-',cv,first) if op2=='r-' else operate(op2,first,cv)
                        if out!=target:continue
                        temp='__fresh_sign_gate__'
                        second=[name,'-',c,temp] if op2=='r-' else [name,op2,temp,c]
                        replacement=data[:index]+[[temp,op1,a,b],second]+data[index+1:]
                        size=live_count(replacement,'P12')
                        if size<original:results.append({'target':name,'first':[op1,a,b],'second':[op2,c],'live':size})
                count_square+=1
                if operate('*',first,first)==target:
                    temp='__fresh_sign_gate__'
                    replacement=data[:index]+[[temp,op1,a,b],[name,'*',temp,temp]]+data[index+1:]
                    size=live_count(replacement,'P12')
                    if size<original:results.append({'target':name,'first':[op1,a,b],'second':['square'],'live':size})
        vals[name]=original_value
    canonical=lambda xs: sorted(json.dumps(x,sort_keys=True) for x in xs)
    return {'eligible':sorted(eligible),'original_live':original,'candidates':canonical(results),
            'first_gates':count_first,'direct_second_tests':count_second,'direct_square_tests':count_square}

start=time.monotonic(); passes={}
for label,ports in [('universal_ports',None),('fixed_ports',fixed)]:
    got=independent_direct(rows,ports); orig=expected[label]
    need(got['eligible']==orig['eligible'] and got['original_live']==orig['original_live'],'class/liveness: '+label)
    need(got['first_gates']==orig['counts']['first_gates'],'first gate enumeration: '+label)
    need(got['candidates']==sorted(json.dumps(c,sort_keys=True) for c in orig['candidates']),'candidate set: '+label)
    need(not orig['counts']['target_zero_samples'] and not orig['counts']['nonconstant_zero_samples'],'zero exclusion: '+label)
    passes[label]=got
# Verify positive control algebraically and by direct enumeration, not just by
# trusting the original search's candidate detection.
index=next(i for i,r in enumerate(rows) if r[0]=='Z')
need(rows[index]==['Z','-','g34','folded_q3Bt'],'control gate changed')
control=rows[:index]+[['__sign_control__','-','folded_q3Bt','g34'],['Z','-',0,'__sign_control__']]+rows[index+1:]
need(live_count(control,'P12')==96,'control not deliberately larger')
for _ in range(3):
    inputs={v:rng.randint(-3,3) for v in variables}
    need(exact_eval(control,inputs)==exact_eval(rows,inputs),'control changed polynomial on test inputs')
control_result=independent_direct(control)
need(any(x['target']=='Z' and x['live']<96 for x in map(json.loads,control_result['candidates'])),'independent positive control missed')
need(control_result['candidates']==sorted(json.dumps(c,sort_keys=True) for c in expected['positive_control']['candidates']),'control candidate set mismatch')

OUT.mkdir(parents=True)
(OUT/'source.py').write_bytes(Path(__file__).read_bytes())
rerun=subprocess.run([sys.executable,'-I','-B',str(SEARCH)],capture_output=True,timeout=180)
(OUT/'search.stdout').write_bytes(rerun.stdout);(OUT/'search.stderr').write_bytes(rerun.stderr)
need(rerun.returncode==0 and not rerun.stderr and rerun.stdout==prior,'recorded search rerun mismatch')
need(SEARCH.read_bytes()==source and BASE.read_bytes()==base and RECORDED.read_bytes()==prior,'source/result drift')
need((SUP/'circuits/positive12_95_degree70.json').read_bytes()==graph_raw and (SUP/'coefficients/BINDING.json').read_bytes()==binding_raw and
    all((SUP/'coefficients'/binding['ports'][name]['file']).read_bytes()==data for name,data in payloads.items()),'input drift')
result={'status':'PASS','source_sha256':SOURCE_SHA,'base_sha256':BASE_SHA,'output_sha256':OUT_SHA,
        'graph_sha256':GRAPH_SHA,'binding_sha256':BINDING_SHA,'prime_verified':P,
        'eligible':sorted(names),'exact_integer_sign_flip_samples':exact_samples,
        'unsquared_consumer_rejected':True,'full_direct_enumeration':passes,
        'control_candidates':len(control_result['candidates']),'control_live_before':96,
        'rerun_exit':rerun.returncode,'rerun_output_identical':True,'inputs_unchanged':True,
        'elapsed_seconds':round(time.monotonic()-start,3),
        'scope':'external finite enumeration; no Lean theorem, full ancestry audit, or global optimality'}
(OUT/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
