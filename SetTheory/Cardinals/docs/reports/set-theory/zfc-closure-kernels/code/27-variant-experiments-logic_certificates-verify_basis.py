#!/usr/bin/env python3
"""Replay a finite implicational proof certificate with structural equality.

No SAT solver, symbolic arithmetic, unification engine, Coq evaluator, or
trusted proof generator is used. The only root is a declared Lukasiewicz
axiom instance; each later row is exactly one modus ponens between two
uniform instances of earlier rows. All checks use explicit exceptions,
so `python -O` does not disable validation.

The proof of this checker's mathematical soundness is induction over rows:
axiom instances are permitted, uniform instances preserve derivations, and
the checked two children have shapes A and A -> B. Thus each row is a
derivable schema for every implication algebra/theorem predicate closed
under the declared axiom and modus ponens. This is executable verification,
not a claim that the checker itself has been proved in Lean or PA.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent

def fail(message):
    raise ValueError(message)

def formula(t, arity):
    if isinstance(t, str):
        if t == 'd':
            return
        if re.fullmatch(r'v\d+', t) and int(t[1:]) < arity:
            return
        fail('out-of-range formula variable')
    if not isinstance(t, list) or len(t) != 2:
        fail('malformed implication tree')
    formula(t[0], arity)
    formula(t[1], arity)

def subst(t, args):
    if isinstance(t, str):
        return t if t == 'd' else args[int(t[1:])]
    return [subst(t[0], args), subst(t[1], args)]

def luk(p, q, r, s):
    return [[[p, q], r], [[r, p], [s, p]]]

def expected_targets():
    p,q,r = 'v0','v1','v2'
    return {
        'K': [p,[q,p]],
        'I': [p,p],
        'Peirce': [[[p,q],p],p],
        'B': [[p,q],[[q,r],[p,r]]],
        'S': [[p,[q,r]],[[p,q],[p,r]]],
    }

def replay(data):
    if data.get('format') != 'implicational-schema-dag-v1':
        fail('unsupported certificate format')
    rows=data.get('rows')
    if not isinstance(rows,list) or not rows:
        fail('empty certificate')
    checked=[]
    def instance(app, arity):
        if not isinstance(app, dict) or set(app) != {'lemma','args'}:
            fail('malformed lemma application')
        n=app['lemma']
        if not isinstance(n,int) or n < 0 or n >= len(checked):
            fail('lemma application is not strictly earlier')
        args=app['args']
        if not isinstance(args,list) or len(args)!=checked[n]['arity']:
            fail('wrong substitution arity')
        for arg in args:
            formula(arg,arity)
        return subst(checked[n]['statement'],args)
    for n,row in enumerate(rows):
        if not isinstance(row,dict) or row.get('id')!=n:
            fail('wrong row index')
        arity=row.get('arity')
        if not isinstance(arity,int) or arity < 0:
            fail('invalid row arity')
        statement=row.get('statement')
        formula(statement,arity)
        proof=row.get('proof')
        if not isinstance(proof,dict):
            fail('malformed proof')
        if proof.get('kind')=='L':
            args=proof.get('args')
            if not isinstance(args,list) or len(args)!=4:
                fail('wrong axiom arity')
            for arg in args:
                formula(arg,arity)
            if luk(*args)!=statement:
                fail('root is not the declared Lukasiewicz axiom')
        elif proof.get('kind')=='mp':
            minor=instance(proof.get('minor'),arity)
            major=instance(proof.get('major'),arity)
            if major != [minor,statement]:
                fail(f'row {n}: modus ponens structural mismatch')
        else:
            fail('unknown inference rule')
        checked.append(row)
    targets=data.get('targets')
    if not isinstance(targets,dict) or set(targets)!=set(expected_targets()):
        fail('wrong target list')
    for name,statement in expected_targets().items():
        n=targets[name]
        if not isinstance(n,int) or n < 0 or n >= len(checked):
            fail('invalid target pointer')
        if checked[n]['statement']!=statement:
            fail('incorrect target formula')
    return {'rows':len(checked),'L_roots':sum(r['proof']['kind']=='L' for r in checked),
            'mp_edges':sum(r['proof']['kind']=='mp' for r in checked),
            'targets':targets}

def mutations(data):
    out=[]
    bad=copy.deepcopy(data); bad['rows'][0]['proof']['args'][0]='v1'
    out.append(('wrong axiom substitution',bad))
    bad=copy.deepcopy(data); bad['rows'][1]['proof']['minor']['lemma']=1
    out.append(('forward/self proof reference',bad))
    bad=copy.deepcopy(data); bad['rows'][1]['proof']['minor']['args'][0]='v0'
    out.append(('wrong MP substitution',bad))
    bad=copy.deepcopy(data); bad['rows'][16]['statement']=['v0','v1']
    out.append(('false K target',bad))
    bad=copy.deepcopy(data); bad['targets']['S']=16
    out.append(('wrong final S pointer',bad))
    bad=copy.deepcopy(data); bad['rows'][2]['proof']['major']['args'].append('d')
    out.append(('extra substitution field',bad))
    return out

def main():
    p=argparse.ArgumentParser()
    p.add_argument('certificate', nargs='?',type=Path,default=BASE/'lukasiewicz_certificate.json')
    p.add_argument('--mutations',action='store_true')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    raw=args.certificate.read_bytes(); data=json.loads(raw)
    result=replay(data)
    result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
    if args.mutations:
        result['mutation_results']=[]
        for name,bad in mutations(data):
            try:
                replay(bad)
            except ValueError as exc:
                result['mutation_results'].append({'case':name,'rejected':True,'reason':str(exc)})
            else:
                fail('mutation was accepted: '+name)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
