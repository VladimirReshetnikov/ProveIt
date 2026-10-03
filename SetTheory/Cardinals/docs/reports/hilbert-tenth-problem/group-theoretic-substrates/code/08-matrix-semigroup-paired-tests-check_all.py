#!/usr/bin/env python3
"""Authored tests; imports only the new sibling compiler and standard library."""
import hashlib
import importlib.util
import itertools
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('paired_authored', ROOT/'paired_compiler.py')
C = importlib.util.module_from_spec(spec); spec.loader.exec_module(C)


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def raises(f, message):
    try:
        f()
    except (ValueError, TypeError, KeyError):
        return
    raise RuntimeError('Expected rejection: '+message)


def generic_product(word, generators):
    # Independent flat 4x4 dot-product implementation.
    result = [int(i==j) for i in range(4) for j in range(4)]
    for name in word:
        b = sum((list(row) for row in generators[name]),[])
        result = [sum(result[4*i+k]*b[4*k+j] for k in range(4))
                  for i in range(4) for j in range(4)]
    return tuple(tuple(result[4*i:4*i+4]) for i in range(4))


def literal_evaluate(exported, values):
    total = 0
    for row in exported['residuals']:
        value = 0
        for term in row['polynomial']:
            product = term['coefficient']
            for var in term['variables']:
                product *= values[var]
            value += product
        total += value**2
    return total


def main():
    if hasattr(sys,'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    k = C.load_constants()
    report = {'source_sha256':C.SOURCE_SHA256,'optimized_python':not __debug__}
    rng = random.Random(20261003)
    polynomials = {(r,mode):C.export(k,r,mode) for r in range(3) for mode in ('signed','natural')}
    for (r,mode), obj in polynomials.items():
        l = obj['ledger']; terms = [t for row in obj['residuals'] for t in row['polynomial']]
        hist = [sum(len(t['variables'])==d for t in terms) for d in range(3)]
        expected_hist = ([4,4,0] if mode=='signed' else [4,8,4]) if r==0 else [r,130*r+928,3656*r-3632+(20 if mode=='natural' else 0)]
        check(hist==expected_hist, f'monomial histogram r={r} {mode}')
        check(l['natural_auxiliary_count']==130*r and l['external_input_count']==(4 if mode=='signed' else 8),'variables')
        check(len(obj['residuals'])==17*r+(4 if mode=='signed' else 8),'residual count')
        check(max(len(t['variables']) for t in terms)*2==(2 if r==0 and mode=='signed' else 4),'degree')
        check(l['literal_residual_monomials_by_degree']==hist,'recomputed term count')
        check(l['generic_sparse_evaluator_multiplications']==sum((d+1)*hist[d] for d in range(3))+len(obj['residuals']),'multiply count')
        check(l['generic_sparse_evaluator_additions']==len(terms)+len(obj['residuals']),'addition count')
    report['literal_small_r_count_and_degree_cases']=len(polynomials)

    zero_cases = 0
    for flat in itertools.product((-1,0,1),repeat=4):
        target = tuple(tuple(k['c'][a][b]+flat[2*a+b] for b in range(2)) for a in range(2))
        for mode in ('signed','natural'):
            cert = C.certificate(k,[],target,mode)
            result = C.evaluate(k,0,cert['values'],mode)
            check(result['zero']==all(v==0 for v in flat),'r0 zero/wrong target')
            check(result['sos']==sum(v*v for v in flat),'r0 exact SOS')
            check(literal_evaluate(polynomials[0,mode],cert['values'])==result['sos'],'r0 literal')
            zero_cases += 1
    report['r0_full_local_target_cube_cases']=zero_cases

    counts={1:0,2:0}; samples={1:[],2:[]}; target_map={}; collisions=[]
    for i in range(1,115):
        samples[1].append([i])
    # Enumerate every r2 product, compare distinct-target count, then evaluate 768 cases.
    for i in range(1,115):
        for j in range(1,115):
            word=[f'A{i}',f'A{j}','C',f'B{j}',f'B{i}']
            full=generic_product(word,k['generators'])
            target=C.target_upper(full)
            if target in target_map:
                collisions.append([target_map[target],[i,j]])
            else:
                target_map[target]=[i,j]
    samples[2] = [[i,i] for i in range(1,115)] + [[i,115-i] for i in range(1,115)]
    samples[2] += [[rng.randrange(1,115),rng.randrange(1,115)] for _ in range(540)]
    for pair in collisions[:4]:
        samples[2].extend(pair)
    for r in (1,2):
        for seq in samples[r]:
            word=[f'A{i}' for i in seq]+['C']+[f'B{i}' for i in reversed(seq)]
            target=C.target_upper(generic_product(word,k['generators']))
            for mode in ('signed','natural'):
                cert=C.certificate(k,seq,target,mode)
                result=C.evaluate(k,r,cert['values'],mode)
                check(result['zero'],'valid sequence rejected')
                check(literal_evaluate(polynomials[r,mode],cert['values'])==0,'literal valid rejected')
                counts[r]+=1
    report['r1_certificate_evaluations']=counts[1]
    report['r2_certificate_evaluations']=counts[2]
    report['r2_all_products_enumerated']=114**2
    report['r2_distinct_targets']=len(target_map)
    report['r2_target_collision_count']=len(collisions)
    report['r2_first_collision']=collisions[0] if collisions else None
    if collisions:
        left,right=collisions[0]
        ca,cb=C.certificate(k,left),C.certificate(k,right)
        check(ca['target']==cb['target'] and ca['values']!=cb['values'],'collision gives distinct roots')

    mutations=0
    for r,seq in [(1,[23]),(2,[114,108])]:
        for mode in ('signed','natural'):
            cert=C.certificate(k,seq,mode=mode)
            for name in C.auxiliary_names(r):
                values=cert['values'].copy(); values[name]+=1
                check(not C.evaluate(k,r,values,mode)['zero'],'single auxiliary mutation accepted')
                mutations+=1
            # Preserve signed differences but violate canonicity.
            for z in ('H','G'):
                for s in range(1,r+1):
                    for a in range(2):
                        for b in range(2):
                            values=cert['values'].copy()
                            values[C.part(z,s,a,b,'p')]+=1; values[C.part(z,s,a,b,'n')]+=1
                            failures=C.evaluate(k,r,values,mode)
                            check(not failures['zero'] and any(x['residual'].startswith('canonical') for x in failures['first_failures']),'noncanonical pair accepted')
                            mutations+=1
            # One-hot sum preserved over Z, but outside the natural domain.
            values=cert['values'].copy(); values[C.selector(1,seq[0])]=2
            alternate=1 if seq[0]!=1 else 2; values[C.selector(1,alternate)]=-1
            raises(lambda:C.evaluate(k,r,values,mode),'negative selectors')
            mutations+=1
            for a in range(2):
                for b in range(2):
                    wrong=[row[:] for row in cert['target']]; wrong[a][b]+=1
                    values=cert['values'].copy(); values.update(C.target_values(wrong,mode))
                    check(not C.evaluate(k,r,values,mode)['zero'],'wrong target accepted')
                    mutations+=1
    # External canonical target invalidity must fail even for equivalent difference.
    for r in range(3):
        cert=C.certificate(k,[1]*r,mode='natural')
        for a in range(2):
            for b in range(2):
                values=cert['values'].copy(); values[f'T_{a}{b}_p']+=1;values[f'T_{a}{b}_n']+=1
                check(not C.evaluate(k,r,values,'natural')['zero'],'noncanonical external target accepted')
                mutations+=1
    report['adversarial_auxiliary_selector_target_mutations']=mutations

    invalid=0
    for r in (-1,True,1.5):
        raises(lambda:C.ledger(k,r),'invalid r');invalid+=1
    for seq in ([0],[115],[True],[-1],[1.2]):
        raises(lambda:C.certificate(k,seq),'invalid tile');invalid+=1
    for target in ([[True,0],[0,1]],[[1,2,3],[4,5,6]],'target'):
        raises(lambda:C.target_values(target),'invalid target type');invalid+=1
    cert=C.certificate(k,[1]); vals=cert['values'].copy();vals.pop('T_00')
    raises(lambda:C.evaluate(k,1,vals),'missing var');invalid+=1
    vals=cert['values'].copy();vals['unexpected']=0
    raises(lambda:C.evaluate(k,1,vals),'extra var');invalid+=1
    vals=cert['values'].copy();vals['e_1_1']=True
    raises(lambda:C.evaluate(k,1,vals),'bool var');invalid+=1
    wrong=[list(row) for row in C.block(k['c'])];wrong[0][2]=1
    raises(lambda:C.target_upper(wrong),'offdiagonal target');invalid+=1
    wrong=[list(row) for row in C.block(k['c'])];wrong[2][2]=2
    raises(lambda:C.target_upper(wrong),'wrong marker target');invalid+=1
    with tempfile.TemporaryDirectory() as d:
        path=Path(d)/'bad.json'; path.write_bytes((ROOT/'data/semigroup.json').read_bytes()+b' ')
        raises(lambda:C.load_constants(path),'source hash');invalid+=1
    raises(lambda:C.target_values(((1,0),(0,1)),'typo'),'unknown target mode');invalid+=1
    report['invalid_input_rejections']=invalid

    # Nonspecialized invalid determinants: theorem proves no roots; test representative prefixes.
    nonsl=0
    for target in [((0,0),(0,0)),((1,0),(0,0)),((2,0),(0,1)),((1,0),(0,-1))]:
        for seq in ([],[1],[114],[1,2],[114,108]):
            cert=C.certificate(k,seq,target)
            check(not C.evaluate(k,len(seq),cert['values'])['zero'],'nonsl target accepted')
            nonsl+=1
    report['nonsl_targets_tested_against_prefixes']=nonsl

    witness=json.loads((ROOT/'data/accepting-witness.json').read_text())
    check(hashlib.sha256((ROOT/'data/accepting-witness.json').read_bytes()).hexdigest()=='13a3857d28b0207d9baa83facac5b2e67bbaeb858d00b82ef9a91c4ab38df890','witness hash')
    seq=witness['inner_tile_sequence'];r=len(seq)
    target=C.target_upper(witness['input']['target'])
    full=generic_product(witness['generator_word'],k['generators'])
    check(full==C.block(target),'independent 189-factor product')
    expected_word=[f'A{i}' for i in seq]+['C']+[f'B{i}' for i in reversed(seq)]
    check(witness['generator_word']==expected_word and r==94,'witness normal form')
    cert=C.certificate(k,seq,target)
    result=C.evaluate(k,r,cert['values'])
    check(result['zero'],'long witness rejected')
    l=C.ledger(k,r)
    check(l['natural_auxiliary_count']==12220 and l['residual_count']==1602,'long ledger')
    natural_values=[cert['values'][name] for name in C.auxiliary_names(r)]
    report['accepting_witness']={'r':r,'generator_factors':len(expected_word),
        'natural_auxiliaries':len(natural_values),'residuals':l['residual_count'],'sos':result['sos'],
        'max_auxiliary_magnitude_bits':max(v.bit_length() for v in natural_values),
        'sum_auxiliary_magnitude_bits':sum(v.bit_length() for v in natural_values),
        'generic_sparse_evaluator_multiplications':l['generic_sparse_evaluator_multiplications'],
        'generic_sparse_evaluator_additions':l['generic_sparse_evaluator_additions']}
    (ROOT/'examples/accepting-94-certificate.json').write_text(json.dumps(cert,indent=2,sort_keys=True)+'\n')
    (ROOT/'examples/accepting-94-ledger.json').write_text(json.dumps(l,indent=2,sort_keys=True)+'\n')
    report['status']='pass'
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
