#!/usr/bin/env python3
"""Independently brute-force small DAGs and rerun the pinned modular search."""
from pathlib import Path
import ast
import gzip
import hashlib
import itertools
import json
import math
import random
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SEARCH = REPO / 'Computability/DiophantineConsistency/research/ordinary12-circuit-local-search/search.py'
OBSERVED = SEARCH.parent / 'observations/search.json'
OUT = HERE / 'observations'
SOURCE_SHA = '98f54938a6eb1a158ffca98581dd5836300e13a6d07f9340ca52ab8ae55f3949'
OUTPUT_SHA = '900114673aa4ee10229634754abfa5af5a02f292c4d29a9af498eddba2e096af'

def sha(data): return hashlib.sha256(data).hexdigest()
def need(ok, msg):
    if not ok: raise AssertionError(msg)

source = SEARCH.read_bytes()
prior = OBSERVED.read_bytes()
need(sha(source) == SOURCE_SHA and sha(prior) == OUTPUT_SHA, 'source/output pin mismatch')
tree = ast.parse(source)
keep = []
for node in tree.body:
    if isinstance(node,(ast.Import,ast.ImportFrom)):
        keep.append(node)
    elif isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in {'PRIME','SAMPLES','SEED'}:
        keep.append(node)
    elif isinstance(node,ast.FunctionDef) and node.name in {'evaluate','live_count','search'}:
        keep.append(node)
scope = {'__file__':str(SEARCH)}
exec(compile(ast.Module(body=keep,type_ignores=[]),str(SEARCH),'exec'),scope)
prime=scope['PRIME']; samples=scope['SAMPLES']; seed=scope['SEED']
need(prime % 4 == 3 and all(prime % x for x in range(2,math.isqrt(prime)+1)), 'prime assumptions')
result_json=json.loads(prior)
sup=REPO/'Computability/DiophantineConsistency/con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
graph_raw=(sup/'circuits/positive12_95_degree70.json').read_bytes()
need(sha(graph_raw)=='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22','graph pin')
graph=json.loads(graph_raw)
binding_raw=(sup/'coefficients/BINDING.json').read_bytes()
need(sha(binding_raw)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01','binding pin')
binding=json.loads(binding_raw)
residues={}
for name in graph['fixed_numerals']:
    row=binding['ports'][name]
    zipped=(sup/'coefficients'/row['file']).read_bytes()
    raw=gzip.decompress(zipped)
    value=int.from_bytes(raw,'little')
    need(sha(zipped)==row['sha256_gzip'] and sha(raw)==row['sha256_raw'] and len(raw)==row['raw_bytes'],'payload pin: '+name)
    need(value.bit_length()==row['bits'] and len(raw)==(value.bit_length()+7)//8,'minimal payload: '+name)
    residues[name]=value%prime
need(residues==result_json['fixed_port_residues'],'fixed residue mismatch')
for key in ('universal_port_search','fixed_port_search'):
    r=result_json[key]
    need(r['original_live']==95 and not r['one_gate_candidates'] and not r['two_gate_candidates'],'unexpected candidates: '+key)
    need(r['counts']['targets']==95 and not r['counts']['targets_with_sample_zero'] and not r['counts']['sample_zero_nonconstant'],'zero/sample count: '+key)

def independently_eval(op, a, b):
    if op == '+': return tuple((x+y)%prime for x,y in zip(a,b))
    if op == '-': return tuple((x-y)%prime for x,y in zip(a,b))
    if op == '*': return tuple((x*y)%prime for x,y in zip(a,b))
    raise AssertionError(op)

def independently_live(rows, out):
    by_name={r[0]:r for r in rows}
    need(len(by_name)==len(rows),'duplicate gate')
    seen=set()
    def visit(x):
        if x not in by_name or x in seen: return
        seen.add(x)
        visit(by_name[x][2]); visit(by_name[x][3])
    visit(out)
    return len(seen)

def all_first_gates(earlier):
    # Commutative cases are canonicalized by earlier-node order, as required
    # to compare candidate sets rather than count mirrored equivalents twice.
    for i,a in enumerate(earlier):
        for b in earlier[i:]:
            yield ('+',a,b)
            yield ('*',a,b)
        for b in earlier:
            yield ('-',a,b)

def brute(rows, variables, output, fixed=None):
    rng=random.Random(seed)
    vals={x:tuple(rng.randrange(1,prime) for _ in range(samples)) for x in variables}
    if fixed:
        vals.update({x:(value % prime,)*samples for x,value in fixed.items()})
    vals.update({i:(i,)*samples for i in range(5)})
    original=independently_live(rows,output)
    one=[]; two=[]
    for i,(name,op,a,b) in enumerate(rows):
        goal=independently_eval(op,vals[a],vals[b]); earlier=list(vals)
        need(all(goal) and all(all(vals[x]) for x in earlier if x != 0),'brute case violates nonzero audit condition')
        gates=list(all_first_gates(earlier))
        for first,x,y in gates:
            fv=independently_eval(first,vals[x],vals[y])
            if fv==goal:
                size=independently_live(rows[:i]+[[name,first,x,y]]+rows[i+1:],output)
                if size<original: one.append({'target':name,'replacement':[first,x,y],'live':size})
            for c in earlier:
                for op2 in ('+','-','r-','*'):
                    rv=independently_eval('-',vals[c],fv) if op2=='r-' else independently_eval(op2,fv,vals[c])
                    if rv!=goal: continue
                    temp='__fresh_local_gate__'
                    second=[name,'-',c,temp] if op2=='r-' else [name,op2,temp,c]
                    size=independently_live(rows[:i]+[[temp,first,x,y],second]+rows[i+1:],output)
                    if size<original: two.append({'target':name,'first':[first,x,y],'second':[op2,c],'live':size})
            if independently_eval('*',fv,fv)==goal:
                temp='__fresh_local_gate__'
                size=independently_live(rows[:i]+[[temp,first,x,y],[name,'*',temp,temp]]+rows[i+1:],output)
                if size<original: two.append({'target':name,'first':[first,x,y],'second':['square'],'live':size})
        vals[name]=goal
    norm=lambda a: sorted(json.dumps(x,sort_keys=True) for x in a)
    return norm(one),norm(two)

tests=[
    ([['a','+','x',1],['b','+','a',1],['c','-','b','x'],['d','*','c','x'],['out','+','d',1]],['x'],'out',None),
    ([['a','+','x',1],['b','+','y',2],['c','*','a','b'],['d','-','c','a'],['out','+','d',3]],['x','y'],'out',None),
    ([['a','+','x',1],['b','*','a','a'],['c','+','b','x'],['out','-','c',1]],['x'],'out',None),
    ([['a','+','x','beta'],['b','*','a','beta'],['c','-','b','x'],['out','+','c',1]],['x','beta'],'out',{'beta':1234}),
]
small=[]
for rows,vars,out,fixed in tests:
    observed=scope['search'](rows,vars,out,fixed)
    expected=brute(rows,vars,out,fixed)
    normalize=lambda a: sorted(json.dumps(x,sort_keys=True) for x in a)
    need((normalize(observed['one_gate_candidates']),normalize(observed['two_gate_candidates']))==expected,'search/brute candidate mismatch')
    need(observed['counts']['targets_with_sample_zero']==0 and observed['counts']['sample_zero_nonconstant']==0,'unexpected zero sample')
    small.append({'rows':len(rows),'fixed':fixed,'one_gate_candidates':len(expected[0]),'two_gate_candidates':len(expected[1]),'match':True})
need(any(x['one_gate_candidates'] for x in small) and any(x['two_gate_candidates'] for x in small),'small graphs lack positive reductions')

# A zero-valued nonconstant node would make multiplication inversion partial.
# The pinned script records both the target-zero and zero-operand condition,
# and its main guard rejects either. Here we test the first part dynamically.
zero_rows=[['zero','-','x','x'],['a','+','x',1],['out','+','zero','a']]
zero=scope['search'](zero_rows,['x'],'out')
need(zero['counts']['targets_with_sample_zero']>0 and zero['counts']['sample_zero_nonconstant']>0,'zero flags did not fire')
need('for tested in (result, fixed_result):' in source.decode() and
     "if tested['counts']['sample_zero_nonconstant'] or tested['counts']['targets_with_sample_zero']:" in source.decode(),'main zero guard missing')

need(not OUT.exists(),'output already exists')
OUT.mkdir(parents=True)
run=subprocess.run([sys.executable,'-I','-B',str(SEARCH)],capture_output=True,timeout=180)
(OUT/'search.stdout').write_bytes(run.stdout)
(OUT/'search.stderr').write_bytes(run.stderr)
need(run.returncode==0 and run.stderr==b'' and run.stdout==prior,'deterministic rerun differs')
need(sha(SEARCH.read_bytes())==SOURCE_SHA and sha(OBSERVED.read_bytes())==OUTPUT_SHA,'input drift')
result={'status':'PASS','source_sha256':SOURCE_SHA,'prior_output_sha256':OUTPUT_SHA,
    'rerun_exit_code':run.returncode,'rerun_sha256':sha(run.stdout),'small_exhaustive_tests':small,
    'zero_target_count':zero['counts']['targets_with_sample_zero'],
    'zero_nonconstant_operand_count':zero['counts']['sample_zero_nonconstant'],
    'prime_verified':prime,'fixed_port_residues':residues,'source_and_prior_unchanged':True,
    'scope':'finite external tests; no Lean theorem or global minimality; fixed port evaluation is at one prime'}
(OUT/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
