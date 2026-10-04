#!/usr/bin/env python3
"""Fresh exact checker; input JSON is inert data, never imported/executed.
Uses only Python standard-library integers and a sparse polynomial ring.
Written independently from the packet's checker. Does not open/run it.
"""
from pathlib import Path
from collections import Counter
from itertools import permutations
import json
import hashlib

SOURCE = Path('/workspace/shared/compatible-homogeneous-realization63-20261004')
OUT = Path(__file__).resolve().parent
INPUTS = ['PROOF.md', 'CERTIFICATE_DAG_SIGNED.json', 'CERTIFICATE_DAG_POSITIVE.json',
          'evidence/diophantine_fixtures.json', 'evidence/static_checks.json']
BEFORE = {name: hashlib.sha256((SOURCE/name).read_bytes()).hexdigest() for name in INPUTS}
checks = []

def require(condition, label):
    if not condition:
        raise AssertionError(label)
    checks.append(label)

# A monomial is a sorted tuple of variable names, repetition means a power.
class P:
    def __init__(self, value=0):
        if isinstance(value, P):
            self.terms = dict(value.terms)
        elif type(value) is int:
            self.terms = {(): value} if value else {}
        elif isinstance(value, str):
            self.terms = {(value,): 1}
        else:
            self.terms = {key: coeff for key, coeff in value.items() if coeff}
    def __add__(self, other):
        other = P(other)
        terms = Counter(self.terms)
        terms.update(other.terms)
        return P(dict(terms))
    __radd__ = __add__
    def __neg__(self):
        return P({m: -c for m, c in self.terms.items()})
    def __sub__(self, other):
        return self + (-P(other))
    def __rsub__(self, other):
        return P(other) - self
    def __mul__(self, other):
        other = P(other)
        result = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                key = tuple(sorted(m+n))
                result[key] = result.get(key, 0) + c*d
        return P(result)
    __rmul__ = __mul__
    def __eq__(self, other):
        return self.terms == P(other).terms
    def __pow__(self, exponent):
        assert type(exponent) is int and exponent >= 0
        result = P(1)
        for _ in range(exponent):
            result = result*self
        return result
    def degree(self):
        return max(map(len, self.terms), default=-1)
    def coefficient(self, *variables):
        return self.terms.get(tuple(sorted(variables)), 0)
    def substitute(self, replacements):
        total = P()
        for monomial, coefficient in self.terms.items():
            term = P(coefficient)
            for variable in monomial:
                term = term*replacements.get(variable, P(variable))
            total = total+term
        return total
    def evaluate(self, values):
        total = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for variable in monomial:
                term *= values[variable]
            total += term
        return total

# Independent determinant implementation: sum over all six permutations.
def determinant(matrix):
    total = 0
    for perm in permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i in range(3) for j in range(i+1, 3))
        term = (-1)**inversions
        for row, col in enumerate(perm):
            term = term*matrix[row][col]
        total = total+term
    return total

def matmul(left, right):
    return [[sum(left[i][k]*right[k][j] for k in range(3)) for j in range(3)] for i in range(3)]

def residuals(matrix):
    g = [P('g'+str(i)) for i in range(1,4)]
    h = [P('h'+str(i)) for i in range(1,4)]
    return [sum(matrix[i][j]*g[j] for j in range(3))-h[i] for i in range(3)] + [
        determinant(matrix)-(2*P('b')-3)*P('d'), (P('b')-1)*(P('b')-2)]

def native_formula(matrix):
    return sum(r*r for r in residuals(matrix))

suffixes = [str(i)+str(j) for i in range(1,4) for j in range(1,4)]
witnesses = ['g1','g2','g3','h1','h2','h3','b','d']
k_inputs = ['k'+s for s in suffixes]
ac_inputs = [prefix+s for s in suffixes for prefix in ['a','c']]
K = [[P('k'+str(i)+str(j)) for j in range(1,4)] for i in range(1,4)]
AC = [[P('a'+str(i)+str(j))-P('c'+str(i)+str(j)) for j in range(1,4)] for i in range(1,4)]

# Basic signed arithmetic regression for the independently implemented ring.
require((P('x')-P('y'))**2 == P({('x','x'):1, ('x','y'):-2, ('y','y'):1}), 'polynomial engine retains negative coefficients')
require(P('x')-P('x') == 0, 'polynomial engine removes exact zero coefficients')


def read_dag(filename, matrix_inputs, counts, residual_nodes, matrix):
    data = json.loads((SOURCE/filename).read_text())
    require(data['positive_witnesses'] == witnesses, filename+': exact eight-witness list')
    require(data['constants'] == [1,2,3], filename+': declared constants')
    expected_inputs = set(matrix_inputs+witnesses)
    env = {name:P(name) for name in expected_inputs}
    nodes = data['nodes']
    ids = []
    actual_inputs, actual_constants = set(), set()
    for node in nodes:
        require(set(node) == {'id','op','left','right'}, filename+': node schema '+node['id'])
        node_id = node['id']
        require(node_id not in env and node_id not in ids, filename+': distinct output '+node_id)
        op = node['op']
        require(op in ('add','sub','mul'), filename+': operation whitelist '+node_id)
        args=[]
        for key in ['left','right']:
            arg=node[key]
            if type(arg) is int:
                require(arg in [1,2,3], filename+': literal constant '+node_id+'/'+key)
                actual_constants.add(arg)
                args.append(P(arg))
            else:
                require(isinstance(arg,str) and arg in env, filename+': topological operand '+node_id+'/'+key)
                if arg in expected_inputs:
                    actual_inputs.add(arg)
                args.append(env[arg])
        left,right=args
        env[node_id] = left+right if op=='add' else left-right if op=='sub' else left*right
        ids.append(node_id)
    require(actual_inputs == expected_inputs, filename+': exact external leaves')
    require(actual_constants == {1,2,3}, filename+': all and only constants 1,2,3 used')
    actual_counts=dict(Counter(n['op'] for n in nodes))
    require(actual_counts == counts == data['operations'], filename+': per-operation ledger')
    require(len(nodes) == sum(counts.values()) == data['total_operations'], filename+': total ledger')
    require(data['output'] == ids[-1], filename+': final output is final node')
    by_id={n['id']:n for n in nodes}
    visited=set()
    def visit(name):
        if not isinstance(name,str) or name not in by_id or name in visited:
            return
        visited.add(name)
        visit(by_id[name]['left'])
        visit(by_id[name]['right'])
    visit(data['output'])
    require(visited == set(ids), filename+': no dead gates')
    expected_residuals=residuals(matrix)
    for index,(node_id,expected) in enumerate(zip(residual_nodes,expected_residuals),1):
        require(env[node_id] == expected, filename+': residual '+str(index)+' exact identity')
    result=env[data['output']]
    require(result == native_formula(matrix), filename+': full polynomial exact identity')
    require(result.degree() == 6, filename+': total degree exactly six')
    return data, env, result, {'external_matrix_inputs':matrix_inputs,'witnesses':witnesses,
        'variable_leaf_count':len(expected_inputs), 'operations':actual_counts,
        'operation_total':len(nodes), 'output':data['output'], 'polynomial_total_degree':result.degree(),
        'polynomial_monomial_count':len(result.terms),
        'residual_degrees':[p.degree() for p in expected_residuals],
        'constants':[1,2,3], 'no_dead_gates':True}

sd,se,signed,signed_report=read_dag('CERTIFICATE_DAG_SIGNED.json', k_inputs,
    {'mul':26,'add':11,'sub':11}, ['v06','v12','v18','v36','v39'], K)
pd,pe,positive,positive_report=read_dag('CERTIFICATE_DAG_POSITIVE.json', ac_inputs,
    {'mul':26,'add':11,'sub':20}, ['v15','v21','v27','v45','v48'], AC)
require(signed.coefficient('k11','k11','k22','k22','k33','k33') == 1, 'signed degree-six nonzero coefficient is 1')
require(positive.coefficient('a11','a11','a22','a22','a33','a33') == 1, 'positive degree-six nonzero coefficient is 1')
subs={k_inputs[i]:P('a'+s)-P('c'+s) for i,s in enumerate(suffixes)}
require(signed.substitute(subs) == positive, 'positive output is exact signed polynomial input substitution')
# Verify that the positive graph is literally the nine differences followed by the same graph.
for index,s in enumerate(suffixes):
    require(pd['nodes'][index] == {'id':'k'+s,'op':'sub','left':'a'+s,'right':'c'+s}, 'positive prefix difference '+s)
rename={node['id']:pd['nodes'][i+9]['id'] for i,node in enumerate(sd['nodes'])}
for i,node in enumerate(sd['nodes']):
    expected={key:(rename.get(value,value) if key in ('id','left','right') else value) for key,value in node.items()}
    require(expected == pd['nodes'][i+9], 'same native graph after nine extra differences '+node['id'])

# Check the literal supplied fixtures without trusting claimed outputs.
fixtures=json.loads((SOURCE/'evidence/diophantine_fixtures.json').read_text())
fixture_results=[]
for fixture in fixtures:
    name=fixture['name']
    sv,pv=fixture['signed_values'],fixture['positive_input_values']
    require(set(sv)==set(k_inputs+witnesses), name+': signed fixture interface')
    require(set(pv)==set(ac_inputs+witnesses), name+': positive fixture interface')
    require(all(type(v) is int for v in sv.values()), name+': signed values are integers')
    require(all(type(v) is int and v>0 for v in pv.values()), name+': positive values are positive integers')
    require(all(sv[w]>0 for w in witnesses), name+': all signed-fixture witnesses positive')
    require(all(pv['a'+s]-pv['c'+s]==sv['k'+s] for s in suffixes), name+': matrix input encoding')
    require(all(sv[w]==pv[w] for w in witnesses), name+': witness equality between encodings')
    rs=[r.evaluate(sv) for r in residuals(K)]
    require(rs==[0]*5, name+': all five residuals zero')
    require(signed.evaluate(sv)==positive.evaluate(pv)==0, name+': both graph outputs zero')
    scale_outputs=[]
    for scale in [2,3,17]:
        scaled=dict(sv)
        scaled.update({w:scale*sv[w] for w in witnesses[:6]})
        value=signed.evaluate(scaled)
        require(value==0, name+': positive scaled fiber '+str(scale))
        scale_outputs.append(value)
    bad_h=dict(sv); bad_h['h1']+=1
    bad_d=dict(sv); bad_d['d']+=1
    bad_b=dict(sv); bad_b['b']=3
    require(signed.evaluate(bad_h)==1, name+': detects changed h1')
    require(signed.evaluate(bad_d)==1, name+': detects changed determinant magnitude')
    require(signed.evaluate(bad_b)>0, name+': rejects b=3')
    fixture_results.append({'name':name,'five_residuals':rs,'signed_output':0,'positive_output':0,
                            'scales_checked':[2,3,17],'scaled_outputs':scale_outputs})

# Centered conversion independently reconstructed from gap definitions.
S=[[1,3,0],[1,-3,3],[1,0,-3]]
B=[[3,3,3],[2,-1,-1],[1,1,-2]]
I9=[[9 if i==j else 0 for j in range(3)] for i in range(3)]
require(matmul(S,B)==I9 and matmul(B,S)==I9, 'centered conversion SB=BS=9I')
require(determinant(S)==27 and determinant(B)==27, 'centered conversion determinants both 27')
M=[[P('m'+str(i)+str(j)) for j in range(1,4)] for i in range(1,4)]
SMB=matmul(matmul(S,M),B)
require(determinant(SMB)==729*determinant(M), 'symbolic det(SMB)=729 det(M)')
centered=native_formula(SMB)
centered_displayed=sum(r*r for r in residuals(SMB)[:3])+(729*determinant(M)-(2*P('b')-3)*P('d'))**2+((P('b')-1)*(P('b')-2))**2
require(centered==centered_displayed, 'centered displayed formula exact identity')
require(centered.degree()==6, 'centered total degree exactly six')
require(centered.coefficient('m11','m11','m22','m22','m33','m33')==531441, 'centered degree-six nonzero coefficient is 729 squared')
require(signed.substitute({'k'+str(i+1)+str(j+1):SMB[i][j] for i in range(3) for j in range(3)})==centered, 'centered formula equals exact native substitution')
center_variables=set(v for monomial in centered.terms for v in monomial)
require(center_variables==set(['m'+s for s in suffixes]+witnesses), 'centered exact nine inputs and eight witnesses; no alias variables')
# Canonical positive-pair encoding of every signed integer is constructive.
for z in range(-25,26):
    a,c=max(z,0)+1,max(-z,0)+1
    require(a>0 and c>0 and a-c==z, 'positive input encoding regression '+str(z))

AFTER={name:hashlib.sha256((SOURCE/name).read_bytes()).hexdigest() for name in INPUTS}
require(BEFORE==AFTER, 'all consumed source bytes unchanged')
report={
    'result':'PASS', 'independent_checker':'Python standard library; sparse exact integer polynomials; permutation determinant',
    'scope':'Native certificate algebra, literal DAG structure/counts/input interfaces, supplied Diophantine fixtures, centered conversion. Physical realization theorem not independently checked here.',
    'source_sha256':BEFORE, 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'signed':signed_report,'positive':positive_report,'fixtures':fixture_results,
    'centered':{'S':S,'B':B,'SB_and_BS':'9I','det_S':27,'det_B':27,'det_SMB_multiplier':729,
        'polynomial_total_degree':centered.degree(),'polynomial_monomial_count':len(centered.terms),
        'degree_six_example_coefficient':531441,'signed_matrix_input_count':9,'positive_witness_count':8,
        'residual_count':5,'literal_operation_count_asserted':False},
    'named_check_count':len(checks),'checks':checks,
    'no_source_or_upstream_programs_executed':True,'no_simulators_schedules_or_Lean_executed':True,
    'source_files_preserved':True}
(OUT/'REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['result','named_check_count','signed','positive','centered']},indent=2))
