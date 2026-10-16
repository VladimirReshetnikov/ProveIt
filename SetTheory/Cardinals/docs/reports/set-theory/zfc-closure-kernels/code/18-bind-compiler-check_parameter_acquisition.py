#!/usr/bin/env python3
"""Check the twelve safe rho8 parameter permutations using the actual emitter.

Here 'safe' means exactly one destructive read of the fourth parameter, the
necessary acquisition condition for the unchanged emission contract. The
Boolean counterexample establishes unsoundness of one excluded rewrite.
This is an executable syntax/semantics audit, not a proof-assistant theorem.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import sys

NAMES=('a','b','c','u')

def rename(f,p):
    return (f[0],*(rename(x,p) for x in f[1:])) if isinstance(f,tuple) else p.get(f,f)

def execute_emission(word):
    """Independent symbolic stack execution with distinct destructive reads."""
    stack=[];counter=0;current_u=None
    for op in word:
        if op in (166,121,168,171):stack.append({166:'a',121:'b',168:'c',171:0}[op])
        elif op==158:counter+=1;current_u='u'+str(counter)
        elif op==208:
            assert stack[-1]==0 and current_u is not None
            stack[-1]=current_u;current_u=None
        elif op==119:
            b=stack.pop();a=stack.pop();stack.append(('imp',a,b))
        else:raise AssertionError('unexpected rho8 emitter token '+str(op))
    assert len(stack)==1 and current_u is None
    return stack[0],counter

def evaluate(f,valuation):
    if isinstance(f,tuple):
        assert f[0]=='imp'
        return not evaluate(f[1],valuation) or evaluate(f[2],valuation)
    return valuation[f]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    if not __debug__:raise RuntimeError('Do not run with -O')
    research=a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC'
    expected={
      'recover_wade_dag.py':'caa4996be46f9201991dba07f81d4673f14e874ac682226c29fce9e0cea851f1',
      'theory_backend_experiment.py':'37043e71a02fba57337040100d79e8f92cba5e2ac5efead816b1522b8663a2e1',
      'pairing_backend_experiment.py':'18f6cf1a50514581834daecd542d9855d07d6c522d4d70f906241de035423572'}
    for name,digest in expected.items():
        if hashlib.sha256((research/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('research source hash mismatch: '+name)
    sys.path.insert(0,str(research))
    import theory_backend_experiment as t
    spec,spec_digest=t.published_spec();row=spec['ax_rows']('a','h','b','c','u')[1]
    records=[];counts=Counter()
    for perm in itertools.permutations(NAMES):
        mapping=dict(zip(NAMES,perm));formula=rename(row,mapping);word=t.emit(formula)
        actual,reads=execute_emission(word)
        assert reads==word.count(158)
        counts[reads]+=1
        records.append({'parameter_permutation':mapping,'destructive_u_reads':reads,
            'unchanged_acquisition_contract':reads==1,'emitted_macro_word':word})
        if reads==1:
            assert rename(actual,{'u1':'u'})==formula
    assert counts=={1:12,2:6,3:6}
    bad={'a':'u','b':'b','c':'c','u':'a'}
    actual,reads=execute_emission(t.emit(rename(row,bad)))
    wanted=('imp',('imp',('imp','c','a'),'u1'),
            ('imp',('imp','u2','c'),('imp','b','c')))
    assert actual==wanted and reads==2
    counterexamples=[]
    for d in (False,True):
        v={'c':False,'b':True,'u1':True,'u2':False,'a':d}
        value=evaluate(actual,v);assert value is False
        counterexamples.append({'valuation':v,'value':value})
    result={'ProveIt_commit':'96836f9eea3540e96322c3d28c7127a582aae223',
        'published_spec_sha256':spec_digest,
        'actual_emitter_sha256':hashlib.sha256((research/'theory_backend_experiment.py').read_bytes()).hexdigest(),
        'rho8_parameter_occurrences':{'a':2,'b':1,'c':3,'u':1},
        'read_count_distribution':dict(counts),'permutations':records,
        'unsafe_permutation':bad,'actual_unsafe_formula':actual,'counterexamples':counterexamples,
        'incoming248_generator_already_checks_single_u_read':True,
        'formal_kernel_proof':False}
    if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'safe':counts[1],'two_reads':counts[2],'three_reads':counts[3],
        'unsafe_formula_boolean_counterexample_verified':True}))

if __name__=='__main__':main()
