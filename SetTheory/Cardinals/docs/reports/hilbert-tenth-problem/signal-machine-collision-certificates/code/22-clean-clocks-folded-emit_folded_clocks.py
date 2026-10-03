#!/usr/bin/env python3
"""Complete native/phase4 circuits with affine constants folded into literals.

Consumes copied frozen JSON references as data. No candidate/base/source module
is imported; standard library only. Base artifacts remain byte-for-byte intact.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
BASE_MANIFEST_PIN='1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95'

def need(condition,why):
    if not condition:
        raise ValueError(why)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def encoded(obj):
    return (json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()

def analyze(p):
    variables=p['parameters']+p['auxiliaries']
    need(len(set(variables))==len(variables),'Distinct ports')
    ds={n:1 for n in variables}
    weights={n:i+2 for i,n in enumerate(variables)}
    cs=dict(weights)
    rows=p['source'];gates={};ops=Counter();constants=set();trace=[];modulus=1000003
    for n,op,a,b in rows:
        need(n not in ds and op in ('+','-','*'),'Fresh gate')
        need(all(type(v)is int or type(v)is str and v in ds for v in (a,b)),'Closed gate')
        da,ca=(ds[a],cs[a]) if type(a)is str else (0,a%modulus)
        db,cb=(ds[b],cs[b]) if type(b)is str else (0,b%modulus)
        d=da+db if op=='*' else max(da,db)
        c=ca*cb if op=='*' else (ca if da==d else 0)+(1 if op=='+' else -1)*(cb if db==d else 0)
        ds[n]=d;cs[n]=c%modulus;gates[n]=(a,b);ops['M' if op=='*' else 'A']+=1
        constants.update(v for v in (a,b) if type(v)is int)
        trace.append([n,d,c%modulus])
    live=set();todo=[p['output']]
    while todo:
        n=todo.pop()
        if type(n)is str and n not in live:
            live.add(n)
            if n in gates:todo.extend(gates[n])
    need(live==set(gates)|set(variables),'All gates and coordinates live')
    need(cs[p['output']]!=0,'Exact-degree lower certificate')
    ledger=dict(total=len(rows),M=ops['M'],A=ops['A'],positive_witnesses=len(p['auxiliaries']),natural_parameters=len(p['parameters']),exact_degree=ds[p['output']],integer_literals=sorted(constants),all_gates_live=True,all_coordinates_live=True,comparisons=len(p['comparisons']),SOS_gates=3*len(p['comparisons'])-1)
    degree=dict(modulus=modulus,substitution_weights=weights,formal_degree=ds[p['output']],nonzero_top_coefficient=cs[p['output']],gate_degree_top_trace=trace)
    return ledger,degree

def build(original,parent_pin,phase):
    p=copy.deepcopy(original)
    rows=p['source']
    index=next(i for i,r in enumerate(rows) if r[0]=='clean_payload_sum0')
    expected=[['clean_payload_sum0','+','final_positive','x'],['clean_payload_sum','+','clean_payload_sum0',1],['clean_endpoint_ticks','*',192,'clean_payload_sum'],['clean_forward_reverse_ticks','*',2,'theta_positive'],['clean_partial_time','+','clean_endpoint_ticks','clean_forward_reverse_ticks'],['clean_native_time','+','clean_partial_time',16]]
    if phase:expected.append(['clean_phase_time','*',4,'clean_native_time'])
    need(rows[index:index+len(expected)]==expected,'Exact inherited bridge')
    factor=4 if phase else 1
    endpoint='clean_phase_time' if phase else 'clean_native_time'
    folded=[['clean_payload_sum0','+','final_positive','x'],['clean_endpoint_ticks','*',192*factor,'clean_payload_sum0'],['clean_forward_reverse_ticks','*',2*factor,'theta_positive'],['clean_partial_time','+','clean_endpoint_ticks','clean_forward_reverse_ticks'],[endpoint,'+','clean_partial_time',208*factor]]
    p['source']=rows[:index]+folded+rows[index+len(expected):]
    need(p['comparisons'][-1]==[endpoint,'Tclean'],'Same exact output row')
    p['format']='complete-unbounded-clean-clock-literal-folded-v1'
    p['model']=('phase4' if phase else 'native-or-spatial-block')+'-literal-folded'
    p['folding_parent_sha256']=parent_pin
    p['folding_base_manifest_sha256']=BASE_MANIFEST_PIN
    p['folded_clock_formula']=f'{192*factor}*(final_positive+x)+{2*factor}*theta_positive+{208*factor}'
    p['all_tuple_identity']='Identical polynomial to the corresponding complete frozen circuit, over every integer assignment of the same ports.'
    p['ledger'],p['exact_degree_certificate']=analyze(p)
    need(p['ledger']['total']==original['ledger']['total']-1-int(phase) and p['ledger']['M']==original['ledger']['M']-int(phase) and p['ledger']['A']==original['ledger']['A']-1,'Exactly one addition saved, plus one multiplication for phase4')
    return p

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    data=(ROOT/'reference/base-MANIFEST.json').read_bytes()
    need(sha(data)==BASE_MANIFEST_PIN,'Frozen base manifest bytes')
    manifest=json.loads(data);outputs={};ledgers={};refs={}
    for name in ('incdec','zero3','nop','positive3'):
        for phase in (False,True):
            mode='phase4' if phase else 'native'
            source=ROOT/'reference'/f'{name}-{mode}.json';data=source.read_bytes();pin=sha(data)
            need(pin==manifest['files'][f'circuits/{name}-{mode}.json']['sha256'],'Copied exact base circuit')
            p=build(json.loads(data),pin,phase);stem=name+'-'+mode+'-folded'
            outputs['circuits/'+stem+'.json']=encoded(p)
            text=['# Complete folded clock DAG. Every +, -, * gate is paid.','# Natural ports: '+', '.join(p['parameters']),'# Strictly positive existential ports: '+', '.join(p['auxiliaries'])]
            text += [f'{n} = {a} {op} {b}' for n,op,a,b in p['source']]
            text += ['# Polynomial output: '+p['output'],'# Required equation: '+p['output']+' = 0']
            outputs['circuits/'+stem+'.dag.txt']=('\n'.join(text)+'\n').encode()
            ledgers[stem]=p['ledger'];refs[source.name]=pin
    receipt=dict(format='folded-clock-emission-v1',base_manifest_sha256=BASE_MANIFEST_PIN,reference_circuits=refs,emitted_files={k:sha(v) for k,v in outputs.items()},ledgers=ledgers,author_or_base_executable_code_run=False)
    outputs['receipts/emission.json']=encoded(receipt)
    for name,data in outputs.items():
        path=ROOT/name
        if args.check:need(path.read_bytes()==data,'Exact emission replay: '+name)
        else:path.write_bytes(data)
    print(json.dumps(dict(status='PASS',mode='replay' if args.check else 'emit',ledgers={k:{n:v[n] for n in ('M','A','total','positive_witnesses','exact_degree')} for k,v in ledgers.items()}),sort_keys=True))

if __name__=='__main__':main()
