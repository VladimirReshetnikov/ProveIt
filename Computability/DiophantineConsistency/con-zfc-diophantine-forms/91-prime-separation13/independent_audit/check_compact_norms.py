#!/usr/bin/env python3
"""Independent exact audits of the compact three/four-radical norms.

Standard library only.  The exact reference is the product of all conjugate
linear factors in a polynomial ring on independent formal square roots.
No numerical samples are used for the polynomial identity claim.
"""
from pathlib import Path
from collections import defaultdict
import ast
import gzip
import importlib.util
import itertools
import json
import random
import hashlib

ROOT=Path(__file__).resolve().parent.parent
NVAR=6
ZERO=(0,)*NVAR

def require(ok,message):
    if not ok: raise ValueError(message)

class Polynomial:
    def __init__(self,value):
        value=value if isinstance(value,dict) else {ZERO:int(value)}
        self.terms={k:v for k,v in value.items() if v}
    @staticmethod
    def coerce(value):
        return value if isinstance(value,Polynomial) else Polynomial(value)
    def __add__(self,other):
        other=self.coerce(other);out=defaultdict(int,self.terms)
        for k,v in other.terms.items():out[k]+=v
        return Polynomial(dict(out))
    __radd__=__add__
    def __neg__(self):return Polynomial({k:-v for k,v in self.terms.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other);out=defaultdict(int)
        for k,v in self.terms.items():
            for l,w in other.terms.items():
                out[tuple(a+b for a,b in zip(k,l))]+=v*w
        return Polynomial(dict(out))
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'nonnegative exponent')
        ans=Polynomial(1);base=self
        while n:
            if n&1:ans=ans*base
            n//=2
            if n:base=base*base
        return ans

def variable(i):
    return Polynomial({tuple(int(k==i) for k in range(NVAR)):1})

class ExactAlgebra:
    def lit(self,n):return Polynomial(n)
    def add(self,a,b):return a+b
    def sub(self,a,b):return a-b
    def mul(self,a,b):return a*b

def conjugate_product(z,roots):
    out=Polynomial(1)
    for signs in itertools.product((-1,1),repeat=len(roots)):
        factor=z
        for sign,root in zip(signs,roots):factor=factor+sign*root
        out=out*factor
    return out

def load_compact_builder():
    spec=importlib.util.spec_from_file_location('audited_compact_builder',ROOT/'new_integer_compact/build.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def universal_identity_checks():
    module=load_compact_builder();algebra=ExactAlgebra()
    z,x1,x2,x3,x4,delta=[variable(i) for i in range(NVAR)]
    reference4=delta**8*conjugate_product(z,[x1,x2,x3,x4])
    actual4=module.norm4(algebra,z,x1*x1,x2*x2,x3*x3,delta*x4*x4,delta)
    require(not (actual4-reference4).terms,'four-root conjugate product identity')
    reference3=delta**4*conjugate_product(z,[x1,x2,x3])
    actual3=module.norm3(algebra,z,x1*x1,x2*x2,delta*x3*x3,delta)
    require(not (actual3-reference3).terms,'three-root conjugate product identity')
    for count,poly in [(4,reference4),(3,reference3)]:
        require(all(all(exponent%2==0 for exponent in key[1:count+1])
                    for key in poly.terms),'radical sign invariance')
    return {
      'method':'exact expansion in Z[z,x1,x2,x3,x4,delta] against every signed linear factor',
      'four_root_identity':True,'four_root_conjugate_factors':16,
      'four_root_expanded_terms':len(reference4.terms),
      'three_root_identity':True,'three_root_conjugate_factors':8,
      'three_root_expanded_terms':len(reference3.terms),
      'rational_radicand_substitution':
        'Cnum=delta*x_last^2; this is an injective polynomial substitution when other radicands are independent squares',
      'all_arithmetic':'exact integers; no floating point or random identity testing'
    }

def quadratic_algebra_checks():
    module=load_compact_builder();base=ExactAlgebra()
    e,o,f,p,b,w=[variable(i) for i in range(NVAR)]
    extension=module.QuadraticAlgebra(base,b)
    x=(e,o);y=(f,p)
    def represented(pair):return pair[0]+w*pair[1]
    def reduce_square(poly):
        out=defaultdict(int)
        for key,value in poly.terms.items():
            key=list(key);power=key[5]//2;key[5]%=2;key[4]+=power
            out[tuple(key)]+=value
        return Polynomial(dict(out))
    require(not (represented(extension.add(x,y))-represented(x)-represented(y)).terms,
            'quadratic addition')
    require(not (represented(extension.sub(x,y))-represented(x)+represented(y)).terms,
            'quadratic subtraction')
    require(not (represented(extension.mul(x,y))-reduce_square(represented(x)*represented(y))).terms,
            'quadratic multiplication')
    require(not (represented(extension.mul(x,x))-reduce_square(represented(x)**2)).terms,
            'quadratic optimized squaring')
    require(not (extension.norm(x)-reduce_square((e+w*o)*(e-w*o))).terms,
            'quadratic norm')
    return {'addition':True,'subtraction':True,'multiplication':True,
        'optimized_squaring':True,'norm':True,
        'ring':'Z[e,o,f,p,b,w]/(w^2-b)',
        'consequence':'Every lifted gate represents the corresponding ordinary polynomial gate; final quadratic norm is its product under w and -w. Combined with the verified norm4 identity, this proves the 32-factor five-root identity.'}

def evaluate(packet,variables,ports,modulus):
    values={'v:'+k:v%modulus for k,v in variables.items()}
    values.update({'c:'+k:v%modulus for k,v in ports.items()})
    def ref(token):
        if token.startswith('n:'):return int(token[2:])%modulus
        require(token in values,'undefined DAG dependency '+token)
        return values[token]
    for node in packet['fixed_recipes']+packet['nodes']:
        left,right=ref(node['left']),ref(node['right'])
        op=node['op'];require(op in ('add','sub','mul'),'allowed operation')
        value=left+right if op=='add' else left-right if op=='sub' else left*right
        values[node['id']]=value%modulus
    return ref(packet['norm_output']),ref(packet['output'])

def coefficient_values():
    folder=ROOT/'new_integer_compression/coefficients'
    out={}
    for name in ('beta','K0','MC','MF','cone_A','cone_B'):
        data=gzip.decompress((folder/(name+'.bin.gz')).read_bytes())
        out[name]=int.from_bytes(data,'little')
    return out

ESSENTIAL_PREFIX={
    'J','q','W','X','Y','E','a','H','Delta','F','R','k','eta','u','A',
    'U','F2','Q','delta','V','D0','det','eta_zeta','t'
}

def definition_closure(packet):
    """Prove every retained abbreviation is a finite integer polynomial.

    Compact and dense circuits intentionally retain different helper cuts.
    This check rejects hidden inputs, division, function calls, variable
    powers, cyclic definitions, and collisions with quantified inputs.
    """
    definitions=packet['polynomial_definitions']
    variables=packet['variables'];ports=packet['fixed_ports']
    require(len(variables)==len(set(variables)),'distinct quantified inputs')
    require(len(ports)==len(set(ports)),'distinct fixed ports')
    require(not set(variables)&set(ports),'variable/port separation')
    leaves=set(variables)|set(ports)
    require(not leaves&set(definitions),'abbreviation/input separation')
    known=leaves|set(definitions)
    def parse(node):
        if isinstance(node,ast.Name):return {node.id}
        if isinstance(node,ast.Constant):
            require(type(node.value) is int,'integer-only constants')
            return set()
        if isinstance(node,ast.UnaryOp):
            require(isinstance(node.op,(ast.USub,ast.UAdd)),'polynomial unary operation')
            return parse(node.operand)
        if isinstance(node,ast.BinOp):
            require(isinstance(node.op,(ast.Add,ast.Sub,ast.Mult,ast.Pow)),
                    'polynomial binary operation')
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant)
                        and type(node.right.value) is int and node.right.value>=0,
                        'fixed nonnegative exponent')
                return parse(node.left)
            return parse(node.left)|parse(node.right)
        raise ValueError('non-polynomial expression node '+type(node).__name__)
    dependencies={}
    for name,expression in definitions.items():
        refs=parse(ast.parse(expression,mode='eval').body)
        require(refs<=known,'hidden abbreviation inputs in '+name+': '+str(sorted(refs-known)))
        dependencies[name]=refs&set(definitions)
    visiting=set();done=set()
    def visit(name):
        if name in done:return
        require(name not in visiting,'cyclic abbreviation '+name)
        visiting.add(name)
        for dep in dependencies[name]:visit(dep)
        visiting.remove(name);done.add(name)
    for name in definitions:visit(name)
    return {'retained_definition_count':len(definitions),'closed':True,
        'acyclic':True,'integer_polynomial_syntax':True,
        'quantified_inputs':len(variables),'fixed_ports':len(ports)}

def compare_definition_scopes(compact,dense,n):
    a=compact['polynomial_definitions'];b=dense['polynomial_definitions']
    common=set(a)&set(b)
    expected=set(ESSENTIAL_PREFIX)
    if n<=14:expected.add('f_center')
    if n==13:expected.update(('c','Bguard'))
    else:expected.update(('G','Pos'))
    if n>=15:expected.add('Strong')
    if n==16:expected.add('Main')
    require(expected<=common,'essential native prefix missing from common definitions')
    require(all(a[key]==b[key] for key in common),'changed common polynomial definition')
    return {'all_common_definitions_identical':True,
        'common_definition_count':len(common),'essential_prefix':sorted(expected),
        'compact_only_helpers':sorted(set(a)-set(b)),
        'dense_only_helpers':sorted(set(b)-set(a)),
        'compact_scope':definition_closure(compact),
        'dense_scope':definition_closure(dense)}

def compare_literals():
    ports=coefficient_values();rng=random.Random(20261023)
    output=[]
    for n,prefix in [(13,'five_root_integer13'),(14,'four_root_integer14'),(15,'three_root_integer15'),(16,'fixed3_crt_integer16')]:
        compact_path=ROOT/'new_integer_compact'/(prefix+'_compact.json')
        dense_path=ROOT/'new_integer_compression'/(prefix+'.json')
        compact=json.loads(compact_path.read_text());dense=json.loads(dense_path.read_text())
        require(set(compact['variables'])==set(dense['variables']),'same variables')
        scopes=compare_definition_scopes(compact,dense,n)
        require(len(compact['nodes'])==compact['operation_count'],'literal gate count')
        tests=0
        for modulus in (1000000007,1000000009):
            for _ in range(64):
                assignment={v:rng.randrange(modulus) for v in compact['variables']}
                actual=evaluate(compact,assignment,ports,modulus)
                expected=evaluate(dense,assignment,ports,modulus)
                require(actual==expected,'compact/dense modular diagnostic mismatch')
                tests+=1
        output.append({'variables':n,'compact_operations':compact['operation_count'],
            'matching_modular_diagnostics':tests,
            'compact_sha256':hashlib.sha256(compact_path.read_bytes()).hexdigest(),
            'dense_sha256':hashlib.sha256(dense_path.read_bytes()).hexdigest(),
            'definition_scope':scopes})
    return output

def polynomial_multiply_mod(a,b,modulus):
    # Kronecker coefficient packing into arbitrary-precision integers.
    # The selected byte width prevents carries between convolution entries.
    bound=min(len(a),len(b))*(modulus-1)**2
    width=max(1,(bound.bit_length()+7)//8)
    aa=int.from_bytes(b''.join(int(x).to_bytes(width,'little') for x in a),'little')
    bb=int.from_bytes(b''.join(int(x).to_bytes(width,'little') for x in b),'little')
    size=len(a)+len(b)-1
    raw=(aa*bb).to_bytes(size*width,'little')
    return [int.from_bytes(raw[i*width:(i+1)*width],'little')%modulus for i in range(size)]

def specialize_dag(packet,ports,slopes,modulus):
    values={'c:'+k:[v%modulus] for k,v in ports.items()}
    values.update({'v:'+k:[0,v%modulus] for k,v in slopes.items()})
    def ref(token):
        return [int(token[2:])%modulus] if token.startswith('n:') else values[token]
    for node in packet['fixed_recipes']+packet['nodes']:
        a,b=ref(node['left']),ref(node['right'])
        if node['op']=='mul':out=polynomial_multiply_mod(a,b,modulus)
        else:
            out=[0]*max(len(a),len(b))
            sign=1 if node['op']=='add' else -1
            for i,x in enumerate(a):out[i]+=x
            for i,x in enumerate(b):out[i]+=sign*x
            out=[x%modulus for x in out]
        while len(out)>1 and not out[-1]:out.pop()
        values[node['id']]=out
    return values[packet['norm_output']],values[packet['output']]

def degree_specialization_checks():
    ports=coefficient_values();results=[]
    references=json.loads((ROOT/'new_integer_compression/DEGREE_LOWER_CERTIFICATES.json').read_text())
    for certificate in references:
        name=certificate['name'];modulus=certificate['prime'];slopes=certificate['slopes']
        compact=json.loads((ROOT/'new_integer_compact'/(name+'_compact.json')).read_text())
        dense=json.loads((ROOT/'new_integer_compression'/(name+'.json')).read_text())
        norm,out=specialize_dag(compact,ports,slopes,modulus)
        dense_norm,dense_out=specialize_dag(dense,ports,slopes,modulus)
        require(norm==dense_norm and out==dense_out,'entire specialized polynomial agrees')
        require(len(out)-1==certificate['specialized_polynomial_degree'],'degree certificate')
        require(out[-1]==certificate['specialized_leading_coefficient'],'leading coefficient certificate')
        results.append({'name':name+'_compact','modulus':modulus,
            'specialized_norm_degree':len(norm)-1,'specialized_degree':len(out)-1,
            'leading_coefficient':out[-1],
            'entire_specialized_polynomial_matches_dense':True,
            'method':'independently implemented exact coefficient convolution via carry-free arbitrary-precision integer packing',
            'claim':'certifies a total-degree lower bound; the upper bound follows from the separately proved universal identity and dense construction degree analysis'})
    return results

def main():
    result={'universal_identities':universal_identity_checks(),
            'quadratic_algebra':quadratic_algebra_checks(),
            'literal_diagnostics':compare_literals(),
            'degree_specializations':degree_specialization_checks(),
            'scope':'Exact norm identities and independent modular checks of literal circuit composition; unbounded arithmetic soundness/completeness is in FOUR_ROOT_REVIEW.md.'}
    (ROOT/'independent_audit/COMPACT_NORM_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
