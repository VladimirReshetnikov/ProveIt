"""Independent authored checks of the new positive12 degree941 circuit."""
import json
from fractions import Fraction
from pathlib import Path
import numpy as np

def require(p, message):
    if not p:
        raise RuntimeError(message)

require(Fraction(9,8)*Fraction(17,16)**3/16 < Fraction(1,8), 'Linear separation constant')
require(Fraction(81,64)*Fraction(17,16)**4/256 < Fraction(1,128), 'Quadratic separation constant')
root=Path(__file__).resolve().parent
packet=json.loads((root.parent/'positive'/'positive12_weight10_ac2_aux_product.json').read_text())
results=[]
for prime,beta in [(1000003,17),(1000033,23),(1000037,31),(1000039,(pow(2,1012115,1000039)-1)%1000039)]:
    def trim(a):
        a=a%prime
        nz=np.flatnonzero(a)
        return a[:int(nz[-1])+1] if len(nz) else np.array([0],dtype=np.int64)
    def plus(a,b,sign):
        c=np.zeros(max(len(a),len(b)),dtype=np.int64)
        c[:len(a)]+=a;c[:len(b)]+=sign*b
        return trim(c)
    values={x:np.array([0,1],dtype=np.int64) for x in packet['witnesses']}
    values.update({x:np.array([v],dtype=np.int64) for x,v in [('beta',beta),('K0',37),('MC',41),('MF',43)]})
    def val(x):return values[x] if isinstance(x,str) else np.array([x],dtype=np.int64)
    for name,op,a,b in packet['source']:
        aa,bb=val(a),val(b)
        # Every input coefficient has magnitude <prime, and convolution
        # length stays below2200, so these integer64 sums are exact.
        require(min(len(aa),len(bb))*(prime-1)**2 < 2**63, 'Integer convolution overflow')
        values[name]=trim(np.convolve(aa,bb)) if op=='*' else plus(aa,bb,1 if op=='+' else -1)
    polynomial=values[packet['output']]
    require(len(polynomial)-1 == 941, 'Unexpected diagonal degree')
    lead=(-pow(2,153,prime)*pow(beta,548,prime)*pow(beta-1,8,prime)*(pow(beta,5,prime)+64))%prime
    require(int(polynomial[-1]) == lead, 'Leading coefficient mismatch')
    results.append({'prime':prime,'beta_residue':beta,'degree':941,'leading_coefficient':lead})
print(json.dumps({'status':'PASS','separation_constants':True,'diagonal_checks':results},indent=2))
