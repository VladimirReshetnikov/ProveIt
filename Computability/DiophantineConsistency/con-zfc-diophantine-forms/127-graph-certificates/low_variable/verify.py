#!/usr/bin/env python3
"""Independent finite algebra audit of the new linear multiplier.

Sparse polynomial utility and coefficient reader are credited adaptations
of the Weak_Carriers source auditor; producer code is never imported.

This file imports neither the producer nor its DAG implementation.  It checks
exact local free-ring identities, the complete three-root norm, coefficient
bytes, topology/liveness, attained leading forms, and targeted corruptions.
It does not mechanize the unbounded arithmetic/calibration proof.
"""
from __future__ import annotations

import argparse
import copy
import gzip
import hashlib
import itertools
import json
import math
import random
from collections import Counter
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parent
VARIABLES = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
EXPECTED_HASHES = {
    'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
    'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
    'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
    'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
    'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
    'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401',
}
EXPECTED = {False: (126, 440), True: (127, 412)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Poly:
    """Sparse commutative Z-polynomial, with literal symbol-name monomials."""
    def __init__(self, terms=0):
        if isinstance(terms, Poly):
            self.t = terms.t
        elif isinstance(terms, int):
            self.t = {(): terms} if terms else {}
        else:
            self.t = {tuple(k): v for k, v in terms.items() if v}

    @staticmethod
    def symbol(name):
        return Poly({(name,): 1})

    def __add__(self, other):
        out = dict(self.t)
        for key, val in Poly(other).t.items():
            out[key] = out.get(key, 0) + val
            if not out[key]:
                del out[key]
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -val for key, val in self.t.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        out = {}
        for left, a in self.t.items():
            for right, b in Poly(other).t.items():
                key = tuple(sorted(left + right))
                out[key] = out.get(key, 0) + a * b
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'bad power')
        result, base = Poly(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base * base
        return result

    def __eq__(self, other):
        return self.t == Poly(other).t


def validate_graph(packet):
    require(packet['schema'] == 'integer-polynomial-dag-v1', 'schema')
    require(packet['domain'] == 'unrestricted integers', 'domain')
    require(packet['variables'] == VARIABLES and packet['variable_count'] == 11,
            'coordinate closure')
    pair = packet['centered']
    require(pair in EXPECTED, 'unknown chart')
    expected_ops, expected_degree = EXPECTED[pair]
    nodes = packet['nodes']
    arithmetic, syntax_degrees = Counter(), []
    found_vars, found_ports = [], []
    for i, node in enumerate(nodes):
        require(isinstance(node, list) and node, 'malformed node')
        op = node[0]
        if op in ('add', 'sub', 'mul'):
            require(len(node) == 3 and all(type(k) is int and 0 <= k < i
                                        for k in node[1:]), 'topology')
            arithmetic[op] += 1
            a, b = (syntax_degrees[k] for k in node[1:])
            syntax_degrees.append(a+b if op == 'mul' else max(a, b))
        else:
            require(op in ('variable', 'coefficient', 'integer') and len(node) == 2,
                    'forbidden node operation')
            if op == 'variable':
                require(node[1] in VARIABLES, 'unknown variable')
                found_vars.append(node[1]); syntax_degrees.append(1)
            elif op == 'coefficient':
                require(node[1] in PORTS, 'unknown coefficient')
                found_ports.append(node[1]); syntax_degrees.append(0)
            else:
                require(type(node[1]) is int, 'noninteger literal')
                syntax_degrees.append(0)
    require(sorted(found_vars) == sorted(VARIABLES), 'missing/duplicate coordinate')
    require(sorted(found_ports) == sorted(PORTS), 'missing/duplicate fixed port')
    output = packet['output']
    require(type(output) is int and 0 <= output < len(nodes), 'bad output')
    live, pending = set(), [output]
    while pending:
        i = pending.pop()
        if i not in live:
            live.add(i)
            if nodes[i][0] in ('add', 'sub', 'mul'):
                pending.extend(nodes[i][1:])
    require(len(live) == len(nodes), 'dead node')
    require(dict(arithmetic) == packet['operation_counts'], 'operation categories')
    require(sum(arithmetic.values()) == packet['operations'] == expected_ops,
            'operation count')
    require(packet['exact_degree'] == expected_degree, 'degree label')
    require(packet['syntactic_degree_bound'] == syntax_degrees[output],
            'syntactic bound')
    for label, index in packet['named_registers'].items():
        require(type(index) is int and 0 <= index < len(nodes), 'bad register index')
        require(packet['register_degree_bounds'][label] == syntax_degrees[index],
                'register degree bound')
    return {'operations': expected_ops, 'exact_degree': expected_degree,
            'syntactic_degree_bound': syntax_degrees[output], 'nodes': len(nodes)}


def check_local_identities(packet):
    nodes, registers = packet['nodes'], packet['named_registers']
    known, checked = {}, []
    x = {name: Poly.symbol('v_'+name) for name in VARIABLES}
    p = {name: Poly.symbol('p_'+name) for name in PORTS}
    for i, node in enumerate(nodes):
        if node[0] == 'variable': known[i] = x[node[1]]
        elif node[0] == 'coefficient': known[i] = p[node[1]]
        elif node[0] == 'integer': known[i] = Poly(node[1])

    def ref(label):
        require(label in checked, 'specification uses an unverified register '+label)
        return known[registers[label]]

    def emit(label, expected):
        require(label in registers, 'missing named register '+label)
        @lru_cache(None)
        def expand(i):
            if i in known: return known[i]
            op, left, right = nodes[i]
            a, b = expand(left), expand(right)
            return a+b if op == 'add' else a-b if op == 'sub' else a*b
        actual = expand(registers[label])
        require(actual == expected, 'free-ring specification mismatch at '+label)
        if registers[label] not in known:
            known[registers[label]] = Poly.symbol('r_'+label)
        checked.append(label)

    symbolic_specification(emit, ref, x, p, packet['centered'])
    require(set(checked) == set(registers), 'unverified/extra named register')
    require(registers['output'] == packet['output'], 'output not bound')
    return len(checked)


def load_coefficients():
    binding = json.loads((ROOT/'coefficients/BINDING.json').read_text())
    require(binding['MF_convention'] == 'MF_native + beta, already shifted', 'MF convention')
    require(set(binding['payloads']) == set(PORTS), 'coefficient port set')
    values, receipts = {}, {}
    for name in PORTS:
        entry = binding['payloads'][name]
        require(entry['file'] == name+'.bin.gz', 'coefficient filename')
        raw = gzip.decompress((ROOT/'coefficients'/entry['file']).read_bytes())
        digest = hashlib.sha256(raw).hexdigest()
        require(digest == entry['raw_sha256'] == EXPECTED_HASHES[name],
                'authenticated payload '+name)
        number = int.from_bytes(raw, 'little')
        require(len(raw) == entry['raw_bytes'] and number.bit_length() == entry['bits'],
                'coefficient size '+name)
        require(raw and raw[-1], 'nonminimal numeral bytes')
        values[name] = number
        receipts[name] = {'bits': number.bit_length(), 'raw_sha256': digest}
    require(values['beta'] == (1 << 1064921)-1, 'beta recipe')
    require(values['cone_A'] == 1 << 1113, 'cone_A recipe')
    require(values['cone_B'] == 1 << 666104, 'cone_B recipe')
    return values, receipts


def symbolic_specification(emit, ref, x, p, centered):
    for key in VARIABLES:
        emit(key, x[key])
    emit('J', 6*x['j']+1)
    emit('qm', p['beta']*ref('J'))
    emit('q', ref('qm')+1)
    emit('q2', ref('q')**2)
    emit('W', 12*x['w']+4)
    emit('X', ref('q')*ref('W'))
    emit('Y', ref('q')*x['v'])
    emit('E', ref('X')*ref('Y'))
    emit('a', ref('E')+ref('Y'))
    emit('H', 4*ref('a')+3)
    emit('Delta', ref('a')**2+ref('H'))
    emit('F', (p['K0']+ref('W'))*x['C']-x['z']*ref('qm'))
    emit('R', (ref('q')*(ref('q')-ref('F'))-x['C'])*(ref('q2')-1)
         +(p['MC']+ref('q')*p['MF'])*ref('J'))
    emit('k', ref('R')+1+x['h']*ref('E'))
    emit('c2', x['c']**2)
    emit('eta', x['c']-ref('Y')*ref('k'))
    emit('error', (p['cone_A']*ref('F')-ref('q'))**2
         +(p['cone_B']*x['C']-ref('q'))**2)
    emit('budget', ref('k')**2*(ref('q2')-ref('error'))
         -4*ref('q2')*ref('eta')**2)
    emit('ell', ref('E')*ref('Y'))
    emit('L', ref('ell')*ref('k'))
    emit('Dt', 1+ref('L')*(ref('L')+ref('k')))
    emit('D81', 243*ref('budget')-324)
    emit('Dg81', 81+ref('D81')*ref('Dt')*x['s']**2)
    emit('P81', ref('Dt')*ref('Dg81'))
    emit('U', x['r']*ref('c2'))
    emit('I2', ref('U')*ref('c2'))
    emit('strong', ref('Delta')*ref('I2'))
    emit('Df', 1+ref('strong'))
    emit('Q', ref('Delta')*ref('strong'))
    emit('delta', ref('Q')-1)
    emit('V', ref('Df')*(x['c']-ref('R')+4*ref('U')*x['T'])-x['c'])
    emit('QV', ref('Q')*ref('V'))
    emit('Cy', ref('QV')*ref('V')-1)
    emit('Da', ref('delta')*ref('Cy'))
    emit('K', ref('X')*(3*x['c']-2*ref('X'))+2)
    emit('M', 2*ref('q2'))
    emit('Dc', ref('M')*ref('H'))
    emit('M2', ref('M')**2)
    emit('M4', ref('M2')**2)
    emit('S', x['s']*x['r']*ref('M4')*ref('Dc'))
    emit('Dc2', ref('Dc')**2)
    emit('Dc3', ref('Dc2')*ref('Dc'))
    emit('zc', ref('Dc')*x['T']+ref('M')*ref('K')+ref('H')*(x['v']-ref('q2')))
    emit('zc2', ref('zc')**2)
    emit('Ac', (ref('zc2')+3*ref('Dc2'))*(ref('zc2')*ref('zc')-19*ref('Dc3')))
    emit('Z', ref('S')*(x['n']+(ref('QV') if centered else 0))-ref('Ac'))
    emit('S2', ref('S')**2)
    emit('S2r', ref('S2')*x['r'])
    emit('AA', 9*ref('S2r')*ref('Df'))
    emit('BB', ref('S2')*ref('Da'))
    emit('GG', ref('S2r')*x['r']*ref('P81'))
    emit('Z2', ref('Z')**2)
    emit('paired', ref('Z2')+ref('AA')-ref('BB')-ref('GG'))
    emit('left', ref('AA')*ref('Z2'))
    emit('right', ref('BB')*ref('GG'))
    emit('inner', ref('paired')**2-4*(ref('left')+ref('right')))
    emit('output', ref('inner')**2-64*ref('left')*ref('right'))


def generic_identities():
    Z,A,B,G=(Poly.symbol(s) for s in ('Z','A','B','G'))
    paired=((Z**2+A-B-G)**2-4*(A*Z**2+B*G))**2-64*A*Z**2*B*G
    symmetric=((Z**2-A-B-G)**2-4*(A*B+A*G+B*G))**2-64*A*B*G*Z**2
    require(paired==symmetric, 'paired norm identity')
    z,a,b,g=(Poly.symbol(s) for s in ('z','a','b','g'))
    product=Poly(1)
    for signs in itertools.product((-1,1),repeat=3):
        product*=z-signs[0]*a-signs[1]*b-signs[2]*g
    converted={}
    for monomial,coefficient in product.t.items():
        counts=Counter(monomial)
        require(all(counts[r]%2==0 for r in ('a','b','g')), 'odd radical survived')
        key=tuple(sorted(('Z',)*counts['z']+('A',)*(counts['a']//2)
                         +('B',)*(counts['b']//2)+('G',)*(counts['g']//2)))
        converted[key]=converted.get(key,0)+coefficient
    require(paired==Poly(converted), 'eight conjugate factor identity')
    require(len(paired.t)==35, 'norm term count')
    S,Q,V=(Poly.symbol(s) for s in ('S','Q','V'))
    require(S**2*(Q-1)*(Q*V**2-1)-(S*Q*V)**2
            == -S**2*(Q*(V**2+1)-1), 'center defect')
    r,c,D,u,T=(Poly.symbol(s) for s in ('r','c','D','u','T'))
    require(1+D*c**4*u**2==1+D*(c**2*u)**2, 'strong square restoration')
    require(4*c**2*u**2*T==4*(c**2*u)*(u*T), 'auxiliary restoration')
    return {'paired_and_symmetric_norm':True,'conjugate_factors':8,
            'collected_norm_terms':35,'center_defect':True,
            'strong_and_auxiliary_restoration':True}


def leading_forms(packet):
    nodes,regs=packet['nodes'],packet['named_registers']
    stop=max(regs[k] for k in ('AA','BB','GG','Z'))
    tops,degrees=[],[]
    for row in nodes[:stop+1]:
        op=row[0]
        if op=='variable': degree,top=1,Poly.symbol('v_'+row[1])
        elif op=='coefficient': degree,top=0,Poly.symbol('p_'+row[1])
        elif op=='integer': degree,top=0,Poly(row[1])
        elif op=='mul':
            a,b=row[1:];degree,top=degrees[a]+degrees[b],tops[a]*tops[b]
        else:
            a,b=row[1:];degree=max(degrees[a],degrees[b])
            aa=tops[a] if degrees[a]==degree else Poly(0)
            bb=tops[b] if degrees[b]==degree else Poly(0)
            top=aa+bb if op=='add' else aa-bb
        require(bool(top.t), 'unhandled leading cancellation in prefix')
        degrees.append(degree);tops.append(top)
    deg=lambda k:degrees[regs[k]]
    top=lambda k:tops[regs[k]]
    required={'I2':5,'U':3,'Df':13,'Q':21,'V':18,'Da':78,'Dt':22,
              'budget':16,'Dg81':40,'P81':62,'S':16,'Ac':35,
              'AA':46,'BB':110,'GG':96}
    for k,v in required.items(): require(deg(k)==v,'degree '+k)
    x={k:Poly.symbol('v_'+k) for k in VARIABLES}
    beta=Poly.symbol('p_beta')
    q0=6*beta*x['j'];X0=12*q0*x['w'];Y0=q0*x['v']
    a0=X0*Y0;R0=-q0**3*(12*x['w']*x['C']-q0*x['z'])
    k0=R0+x['h']*a0
    B0=2**14*x['s']**2*x['r']**6*q0**20*a0**14*x['c']**16*R0**2
    G0=-2**16*3**5*x['s']**4*x['r']**4*q0**22*X0**6*Y0**12*k0**6
    require(top('BB')==B0,'entire auxiliary leading form')
    require(top('GG')==G0,'entire fused leading form')
    if packet['centered']:
        center_deg=deg('S')+deg('Q')+deg('V')
        omega=max(70,center_deg+35,2*deg('S')+deg('Q')+2*deg('V'))
        bracket=deg('BB')+deg('GG')
        competitors=[2*max(omega,deg('AA'),deg('GG')),
                     deg('AA')+deg('BB'),deg('AA')+deg('GG')]
        require(all(d<bracket for d in competitors),'bracket leading competitor')
        correction=deg('AA')+deg('BB')+deg('GG')+2*deg('Z')
        degree=2*bracket
        require(correction<degree,'outer correction competitor')
        final_top=16*B0**2*G0**2
        expected=(2**64*3**10*x['s']**12*x['r']**20*x['c']**32
                  *q0**84*X0**40*Y0**52*R0**4*k0**12)
        require(final_top==expected,'whole centered leading form')
        exponents={'j':216,'w':52,'v':64,'h':12,'z':4,'s':12,'r':20,'c':32}
        p2,p3,pbeta=384,278,216
        extra={'omega_upper_bound':omega,'inner_bracket_degree':bracket,
               'other_bracket_degree_bounds':competitors,'correction_degree':correction}
    else:
        require(deg('BB')>max(2*deg('Z'),deg('AA'),deg('GG')),'direct leading term')
        degree=4*deg('BB');final_top=B0**4
        correction=deg('AA')+deg('BB')+deg('GG')+2*deg('Z')
        require(correction<degree,'direct correction competitor')
        exponents={'j':224,'w':56,'v':56,'z':8,'s':8,'r':24,'c':64}
        p2,p3,pbeta=392,280,224
        extra={'highest_form':'BB_top**4','correction_degree':correction}
    key=['p_beta']*pbeta
    for variable,e in exponents.items():key+=['v_'+variable]*e
    require(final_top.t.get(tuple(sorted(key)))==2**p2*3**p3,'attained coefficient')
    require(sum(exponents.values())==degree==packet['exact_degree'],'exact degree')
    return {'exact_degree':degree,'prefix_degrees':required,'attained_monomial':exponents,
            'attained_coefficient':{'power_of_2':p2,'power_of_3':p3,'power_of_beta':pbeta},
            'whole_leading_form_terms':len(final_top.t),**extra}


def mutation_controls(packet):
    bad=[]
    for name in ('I2','V','S','AA','BB','GG','output'):
        altered=copy.deepcopy(packet)
        row=altered['nodes'][altered['named_registers'][name]]
        require(row[0] in ('add','sub','mul'),'mutation target')
        row[0]='sub' if row[0]!='sub' else 'add'
        try:check_local_identities(altered)
        except ValueError:bad.append(name)
        else:raise ValueError('accepted corrupted circuit at '+name)
    return bad


def bounded_controls():
    cases=0
    for A,c,r in itertools.product(range(2,24,3),range(-5,6),range(-12,13)):
        if r==0:continue
        Delta=A*A-1;Df=1+Delta*c**4*r;Q=Delta**2*c**4*r
        require(Df%3==1,'strong modulus')
        if c:
            require(r*Df>0,'strong product positivity')
        for T,R in itertools.product(range(-2,3),range(-2,3)):
            V=Df*(c-R+4*c*c*r*T)-c
            Da=(Q-1)*(Q*V*V-1)
            require(Da>0 and Da%3==1,'auxiliary positivity/unit')
            cases+=1
    # This is a finite transcription control, not a proof of separation.
    for a,b in itertools.product(range(40),repeat=2):
        if a%2!=b%2:continue
        eps=a%2
        require(1+(a-eps)//2 < 2+a+(b-eps)//2,'valuation order')
    return {'signed_radical_cases':cases,'valuation_boundary_controls':True,
            'scope':'finite regression only; unbounded proof in PROOF.md'}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    _,coeffs=load_coefficients()
    ledger=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
    for entry in ledger['source_files']:
        data=(ROOT/entry['file']).read_bytes()
        require(len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],
                'retained source identity '+entry['file'])
    result={'checker':'no producer import; exact sparse integer algebra',
            'scope':'finite circuit algebra, coefficients and degrees; unbounded proof separate',
            'coefficients':coeffs,'generic':generic_identities(),
            'authenticated_source_files':len(ledger['source_files']),
            'bounded_controls':bounded_controls(),'variants':[]}
    for centered in (False,True):
        name='linear_multiplier11_'+('centered412' if centered else 'direct440')+'.json'
        packet=json.loads((ROOT/name).read_text())
        result['variants'].append({'file':name,**validate_graph(packet),
            'register_identities':check_local_identities(packet),
            'degree_certificate':leading_forms(packet),
            'rejected_corruptions':mutation_controls(packet)})
    result['passed']=True
    data=json.dumps(result,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(data)
    print(data)

if __name__=='__main__':main()


