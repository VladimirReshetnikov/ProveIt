"""Add three-square guards to original free inputs, retaining degree four.

Gate nonnegativity follows by reversing the certified eliminations and then
using induction through the original nonnegative arithmetic gates.
"""
import argparse
import copy
from hashlib import sha256
import json
from pathlib import Path
from build import census,write
from compress import expand,terms


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=Path(__file__).parent/'final')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    outdir=a.output or a.input/'integer'
    outdir.mkdir(parents=True,exist_ok=True)
    source=(a.input/'equation.json').read_bytes()
    eq=copy.deepcopy(json.loads(source))
    eq.pop('metrics',None)
    free=[i for i,v in enumerate(eq['variables']) if v['kind']!='gate']
    guards=[]
    for i in free:
        ids=[]
        for s in ('a','b','c'):
            ids.append(len(eq['variables']))
            eq['variables'].append({'name':'nonnegative.'+str(i)+'.'+s,'kind':'integer_square'})
        row={'label':'nonnegative.'+str(i),
             'terms':[[3,[]],[8,[i]]]+[[-1,[v,v]] for v in ids]}
        eq['residuals'].append(row)
        guards.append({'input':i,'square_variables':ids})
    eq['domain']='unrestricted integers'
    eq['variant']='cofinal11_shared_pell_integer'
    poly=expand(eq)
    metrics=census(eq,poly)
    eq['metrics']=metrics
    hashes={}
    hashes['equation.json']=write(outdir/'equation.json',eq)
    hashes['expanded_polynomial.json']=write(outdir/'expanded_polynomial.json',
        {'schema':'sparse_integer_polynomial_v1','domain':'unrestricted integers',
         'variables':len(eq['variables']),'terms':terms(poly)})
    hashes['guard_certificate.json']=write(outdir/'guard_certificate.json',
        {'schema':'three_square_input_guards_v1','source_sha256':sha256(source).hexdigest(),
         'natural_variables':len(json.loads(source)['variables']),'guards':guards})
    result={'status':'BUILT','metrics':metrics,'guarded_inputs':len(free),
            'added_variables':3*len(free),'sha256':hashes,
            'scope':'Literal integer quartic; natural equivalence uses Legendre three-square theorem and retained gate definitions.'}
    (outdir/'BUILD.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__': main()
