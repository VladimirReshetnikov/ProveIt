#!/usr/bin/env python3
"""Emit the 36-variable integer lift of the fixed twelve-positive polynomial."""
from pathlib import Path
from collections import Counter
import copy, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'compact/fixed_12_rational_74_degree438.json'
OUTPUT=ROOT/'equations/P36_integer.json'

def build():
    parent=json.loads(PARENT.read_text())
    if parent['domain']!='strictly positive integers' or len(parent['witnesses'])!=12:
        raise ValueError('Unexpected positive parent')
    inputs=[];prefix=[];substitutions={}
    for x in parent['witnesses']:
        a,b,c=(x+'_'+suffix for suffix in ('a','b','c'))
        inputs.extend((a,b,c))
        prefix.extend([
            [x+'__a2','*',a,a],
            [x+'__b2','*',b,b],
            [x+'__c1','+',c,1],
            [x+'__cc1','*',c,x+'__c1'],
            [x+'__ab','+',x+'__a2',x+'__b2'],
            [x+'__abc','+',x+'__ab',x+'__cc1'],
            [x,'+',x+'__abc',1],
        ])
        substitutions[x]={'coordinates':[a,b,c],
                          'formula':'1+a^2+b^2+c*(c+1)'}
    source=prefix+copy.deepcopy(parent['source'])
    binding=copy.deepcopy(parent['coefficient_binding'])
    binding['path']='../compact/coefficients/'
    binding['recipe']='../compact/rebuild_fixed_coefficients.py'
    binding['ordinary_proof']='../compact/FIXED_CARRIER_PROOF.md'
    packet={
        'schema':'integer_polynomial_dag_v1',
        'name':'P36_integer',
        'domain':'unrestricted integers',
        'witnesses':inputs,
        'fixed_numerals':parent['fixed_numerals'],
        'coefficient_binding':binding,
        'source':source,'output':parent['output'],
        'operations':len(source),
        'operation_counts':dict(Counter(row[1] for row in source)),
        'exact_degree':876,
        'parent':'../compact/fixed_12_rational_74_degree438.json',
        'parent_sha256':hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        'substitutions':substitutions,
        'transformation':
            'Replace each positive coordinate x by 1+a^2+b^2+c*(c+1), with three independent integer coordinates.',
        'proof':{
            'positive_range':'c*(c+1)>=0 for every integer c.',
            'surjectivity':
                'For N>=1, the three-square theorem applies to 4*(N-1)+1. Exactly one representing square is odd; division by 4 after subtracting 1 gives N=1+a^2+b^2+c*(c+1).',
            'exact_degree':
                'The parent degree 438 homogeneous part is nonzero. Each substitution has leading part a^2+b^2+c^2; retaining only a-coordinates gives the injective substitution x->a^2, so degree 876 is attained.',
            'nonzero_coefficient':'+24*beta^272',
            'monomial':{'J_a':544,'w_a':80,'s_a':154,'eta_a':74,
                        'i_a':16,'T_a':4,'gamma_a':2,'z_a':2},
            'consistency_calibration':
                'Zero-existence equivalence composes with the retained ordinary positive-parent proof; this lift adds no new end-to-end formal proof certificate.',
        },
    }
    OUTPUT.parent.mkdir(parents=True,exist_ok=True)
    OUTPUT.write_text(json.dumps(packet,indent=2)+'\n')
    return {'file':str(OUTPUT.relative_to(ROOT)),
            'variables':len(inputs),'operations':len(source),
            'operation_counts':packet['operation_counts'],'exact_degree':876,
            'sha256':hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}

if __name__=='__main__':
    print(json.dumps(build(),indent=2))
