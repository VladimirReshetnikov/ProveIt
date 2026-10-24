#!/usr/bin/env python3
"""Independent offline checker for the centered twelve-positive circuits.

Standard library only. Does not import build.py or execute upstream programs.
Exact expansion stops at the two outer carriers; the large norm is checked
at an independent four-variable cut, with an exact weighted leading form.
These finite checks do not prove the inherited unbounded compiler theorem.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path
import random

VARS = ['j','F','alpha','i','T','X','Y','r','eta','zeta','n','gamma']
PORTS = ['beta','K0','MC','MF']

def require(condition, message):
    if not condition:
        raise ValueError(message)

class Ring:
    def __init__(self, names):
        self.names = tuple(names)
        self.zero = (0,) * len(names)
    def c(self, value):
        require(type(value) is int, 'non-integer polynomial coefficient')
        return Poly(self, {} if value == 0 else {self.zero:value})
    def v(self, name):
        powers = [0] * len(self.names)
        powers[self.names.index(name)] = 1
        return Poly(self, {tuple(powers):1})

class Poly:
    def __init__(self, ring, terms):
        self.ring = ring
        self.terms = {m:c for m,c in terms.items() if c}
    def promote(self, other):
        return self.ring.c(other) if type(other) is int else other
    def __add__(self, other):
        other = self.promote(other)
        require(other.ring is self.ring, 'different polynomial rings')
        out = self.terms.copy()
        for m,c in other.terms.items(): out[m] = out.get(m,0) + c
        return Poly(self.ring,out)
    __radd__ = __add__
    def __neg__(self): return Poly(self.ring,{m:-c for m,c in self.terms.items()})
    def __sub__(self, other): return self + (-self.promote(other))
    def __rsub__(self, other): return self.promote(other) + (-self)
    def __mul__(self, other):
        other = self.promote(other)
        require(other.ring is self.ring, 'different polynomial rings')
        out = {}
        for u,a in self.terms.items():
            for v,b in other.terms.items():
                w = tuple(x+y for x,y in zip(u,v))
                out[w] = out.get(w,0) + a*b
        return Poly(self.ring,out)
    __rmul__ = __mul__
    def __pow__(self, exponent):
        require(type(exponent) is int and exponent >= 0, 'bad exponent')
        base, result = self, self.ring.c(1)
        while exponent:
            if exponent & 1: result = result*base
            exponent >>= 1
            if exponent: base = base*base
        return result
    def __eq__(self, other):
        other = self.promote(other)
        return isinstance(other,Poly) and self.ring is other.ring and self.terms == other.terms
    def degree(self, weights):
        return max((sum(e*w for e,w in zip(m,weights)) for m in self.terms), default=-1)
    def lead(self, weights):
        d = self.degree(weights)
        return Poly(self.ring,{m:c for m,c in self.terms.items()
                              if sum(e*w for e,w in zip(m,weights)) == d})
    def coefficient(self, powers):
        m = tuple(powers.get(name,0) for name in self.ring.names)
        return self.terms.get(m,0)

def operate(op, a, b):
    if op == '+': return a+b
    if op == '-': return a-b
    if op == '*': return a*b
    raise ValueError('unsupported operation')

def ancestors(packet, roots, cuts=()):
    rows = {row[0]:row for row in packet['source']}
    found = set()
    def visit(name):
        if type(name) is int or name in found: return
        found.add(name)
        if name in cuts: return
        if name in rows:
            visit(rows[name][2]); visit(rows[name][3])
    for root in roots: visit(root)
    return found

def evaluate(packet, values, roots, modulus=None):
    rows = {row[0]:row for row in packet['source']}
    cache = dict(values)
    def ev(name):
        if type(name) is int: return name
        if name not in cache:
            require(name in rows, 'unbound cut input '+name)
            _,op,a,b = rows[name]
            val = operate(op,ev(a),ev(b))
            cache[name] = val if modulus is None else val % modulus
        return cache[name]
    return {name:ev(name) for name in roots}

def schema(packet):
    require(packet['domain'] == 'strictly positive integers', 'wrong domain')
    require(packet['witnesses'] == VARS, 'wrong witnesses/order')
    require(packet['fixed_numerals'] == PORTS, 'wrong fixed ports/order')
    require(packet['residuals'] == ['A0','A1','N'], 'wrong residual interface')
    known = set(VARS+PORTS)
    require(type(packet['source']) is list, 'source is not a list')
    for row in packet['source']:
        require(type(row) is list and len(row)==4, 'invalid row')
        name,op,a,b = row
        require(type(name) is str and name not in known, 'duplicate/non-string target')
        require(type(op) is str and op in ['+','-','*'], 'invalid operation')
        for operand in [a,b]:
            require(type(operand) is int or (type(operand) is str and operand in known),
                    'invalid or forward operand')
        known.add(name)
    require(packet['output'] in known, 'missing output')
    live = ancestors(packet,[packet['output']])
    require(set(VARS+PORTS) <= live, 'dead declared input')
    require(all(row[0] in live for row in packet['source']), 'dead operation')
    count = len(packet['source'])
    breakdown = dict(Counter(row[1] for row in packet['source']))
    core = ancestors(packet,packet['residuals'])
    core_count = sum(row[0] in core for row in packet['source'])
    require(type(packet['operations']) is int and packet['operations']==count,
            'operation metadata mismatch')
    require(packet['operation_breakdown']==breakdown, 'breakdown metadata mismatch')
    require(type(packet['system_operations']) is int and packet['system_operations']==core_count,
            'system operation metadata mismatch')
    return {'operations':count,'system_operations':core_count,'breakdown':breakdown}

def outer_formula(v):
    j,F,alpha,i,T,X,Y,r,eta,zeta,n,gamma = [v[k] for k in VARS]
    beta,K0,MC,MF = [v[k] for k in PORTS]
    J=6*j+1; q=beta*J+1; C=q-F-alpha
    k=eta+zeta; c=k*Y+eta; a=(X+1)*Y; H=4*a+3
    Delta=(a+2)**2-1; ell=X*Y**2*k
    W=(q-1)*k+1; M0=q**3*(q-1)
    Bt=(q*K0+X)*C-q*F
    Z=M0*(ell+k+r)+(q-1)*Y-q**3*W*Bt
    A0=Z**2-M0**2*(ell*(ell+k)+1)
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    r0=k-R-1; U=q*q*Y; L=q*Y
    Dstar=U*(X+a*c)+H*(U*gamma+L*X-r0)
    A1=Dstar**2-U**2*(1+Delta*c*c)
    I=i*c*c
    D=1+Delta*I*I; Q=Delta*Delta*I*I; d=Q-1
    f0=(a+2)*I; e=1-I*I; V=D*(c*T-R)-c
    return locals()

def check_exact_outer(packet):
    ring = Ring(VARS+PORTS)
    v = {name:ring.v(name) for name in ring.names}
    # No outer expansion of N is performed here.
    form = outer_formula(v)
    names = ['J','q','C','k','c','a','H','Delta','ell','W','M0','Bt','Z',
             'A0','R','r0','U','L','Dstar','A1','I','D','Q','d','f0','V']
    literal = evaluate(packet,v,names)
    for name in names:
        require(literal[name] == form[name], 'outer formula mismatch at '+name)
    weights = [1]*len(VARS)+[0]*len(PORTS)
    require(form['A0'].degree(weights)==15, 'A0 degree')
    require(form['A1'].degree(weights)==13, 'A1 degree')
    ql=6*v['beta']*v['j']; kl=v['eta']+v['zeta']
    Btl=(ql*v['K0']+v['X'])*(ql-v['F']-v['alpha'])-ql*v['F']
    Rl=ql**3*(ql-v['F'])
    lead0=-2*ql**8*v['X']*kl**2*v['Y']**2*Btl
    lead1=8*ql**2*v['X']**2*v['Y']**4*kl*(ql**2*v['Y']*v['gamma']+Rl)
    leadN=4*v['X']**12*v['Y']**32*v['i']**10*kl**20*Rl**2
    require(form['A0'].lead(weights)==lead0, 'A0 leading form')
    require(form['A1'].lead(weights)==lead1, 'A1 leading form')
    require(form['V'].degree(weights)==18, 'V degree')
    require(form['V'].lead(weights)==-form['Delta'].lead(weights)*form['I'].lead(weights)**2*Rl,
            'V leading substitution')
    # Weighted-cut leading coefficient from check_norm_cut, composed here.
    require(leadN.degree(weights)==82, 'composed norm degree')
    return ring, v, lead0, lead1, leadN, {
        'matched_outer_registers':len(names),
        'A0_terms':len(form['A0'].terms),
        'A1_terms':len(form['A1'].terms),
        'V_terms':len(form['V'].terms),
        'residual_degrees':[15,13,82],
    }

def check_norm_cut(packet):
    ring = Ring(['a','I','V','n'])
    a,I,V,n = [ring.v(name) for name in ring.names]
    values=dict(zip(ring.names,[a,I,V,n]))
    actual=evaluate(packet,values,['N'])['N']
    A=a+2; Delta=A*A-1; D=1+Delta*I*I
    Q=Delta*Delta*I*I; d=Q-1; f0=A*I; e=1-I*I
    x=n+f0+V; B=2*d*x
    H=d*(n*n+2*V*n+e)-V*V+1
    centered=H*H+2*B*f0*H-B*B*e
    C=H+B*f0
    require(actual==centered, 'literal/centered norm identity')
    require(centered==C*C-B*B*D, 'square identity')
    require(C==d*(x*x+D)-Q*V*V+1, 'inverse recovery identity')
    weights=[2,5,18,1]
    require(actual.degree(weights)==82, 'weighted norm-cut degree')
    require(actual.lead(weights)==4*a**8*I**6*V**2, 'weighted norm-cut leader')
    # Independently checked exceptional-locus identity.
    rb=Ring(['A','I','n'])
    aa,ii,nn=[rb.v(t) for t in rb.names]
    de=aa*aa-1; dd=1+de*ii*ii; qq=de*de*ii*ii; vv=-nn-aa*ii
    hh=(qq-1)*(nn*nn+2*vv*nn+1-ii*ii)-vv*vv+1
    require(hh==de*ii*ii*(de*(dd-vv*vv)-1), 'B=0 exclusion identity')
    return {'abstract_norm_variables':list(ring.names),'abstract_norm_terms':len(actual.terms),
            'weighted_degree':82,'unique_weighted_leading_term':'4*a^8*I^6*V^2',
            'full_outer_norm_expanded':False}

def check_finalizer(packet, ring, lead0, lead1, leadN):
    cut=Ring(['A0','A1','N']); u,v,w=[cut.v(n) for n in cut.names]
    actual=evaluate(packet,dict(zip(cut.names,[u,v,w])),[packet['output']])[packet['output']]
    if actual==(1+u)*(1+v)*(1+w)-1:
        mode='product'; degree=110; leading=lead0*lead1*leadN
        powers={'j':18,'F':2,'alpha':1,'gamma':1,'i':10,'X':16,'Y':39,'eta':23,'beta':18}
        coeff=64*6**18
        descr='64*(6*beta)^18 at j^18 F^2 alpha gamma i^10 X^16 Y^39 eta^23'
    elif actual==u*u+v*v+w*w:
        mode='sos'; degree=164; leading=leadN*leadN
        powers={'j':12,'F':4,'i':20,'X':24,'Y':64,'eta':40,'beta':12}
        coeff=16*6**12
        descr='16*(6*beta)^12 at j^12 F^4 i^20 X^24 Y^64 eta^40'
    else: raise ValueError('unrecognized literal finalizer')
    require(leading.coefficient(powers)==coeff, 'exact leading-monomial certificate')
    require(packet['exact_degree']==degree, 'degree metadata mismatch')
    require(packet['residual_degrees']==[15,13,82], 'residual degree metadata')
    return {'mode':mode,'exact_degree':degree,'leading_terms':len(leading.terms),
            'nonzero_actual_coefficient_certificate':descr}

def coefficients(root):
    path=root/'coefficients'/'COEFFICIENT_BINDING.json'
    binding=json.loads(path.read_text())
    values={}; evidence=[]
    rename={'beta':'beta','K':'K0','MC':'MC','MF_source':'MF'}
    for item in binding['materialization']['files']:
        rel=Path(item['file']); fp=(root/rel).resolve()
        require(root.resolve() in fp.parents, 'coefficient path escapes packet')
        packed=fp.read_bytes(); raw=gzip.decompress(packed)
        require(hashlib.sha256(packed).hexdigest()==item['gzip_sha256'], 'compressed hash')
        require(hashlib.sha256(raw).hexdigest()==item['sha256'], 'raw hash')
        val=int.from_bytes(raw,'little')
        require(val.bit_length()==item['bits'], 'coefficient bits')
        require(len(raw)==item['raw_bytes'] and raw[-1]!=0, 'nonminimal coefficient bytes')
        values[rename[item['port']]]=val
        evidence.append({'port':rename[item['port']],'bits':val.bit_length(),'sha256':item['sha256']})
    require(set(values)==set(PORTS), 'incomplete tuple')
    d=binding['d']; beta=values['beta']; native=values['MF']-beta
    require(beta==(1<<d)-1, 'radix coefficient')
    require(beta%3==1, 'beta modulo three')
    require(0<values['MC']<beta and 0<native<beta, 'native mask bounds')
    require(values['MC'].bit_count()+native.bit_count()==d, 'mask population')
    return values,evidence

def modular_checks(packet, fixed):
    rng=random.Random(124110)
    primes=[2147483647,2305843009213693951]
    count=0; mod4=0
    for prime in primes:
        for test in range(32):
            vals={v:rng.randrange(-20,41) for v in VARS}
            vals.update({k:x%prime for k,x in fixed.items()})
            f=outer_formula(vals)
            n=vals['n']; x=n+f['f0']+f['V']; B=2*f['d']*x
            H=f['d']*(n*n+2*f['V']*n+f['e'])-f['V']**2+1
            N=H*H+2*B*f['f0']*H-B*B*f['e']
            literal=evaluate(packet,vals,['A0','A1','N',packet['output']],prime)
            for name, expected in [('A0',f['A0']),('A1',f['A1']),('N',N)]:
                require(literal[name]==expected%prime, 'actual-tuple modular mismatch '+name)
            a,b,c=[literal[k] for k in ['A0','A1','N']]
            expected=(a*a+b*b+c*c if packet['exact_degree']==164 else (1+a)*(1+b)*(1+c)-1)
            require(literal[packet['output']]==expected%prime,'modular finalizer')
            count+=1
    # Actual fixed coefficients reduced modulo four suffice for this congruence.
    for _ in range(128):
        vals={v:rng.randrange(1,30) for v in VARS}
        vals.update({k:x%4 for k,x in fixed.items()})
        residuals=evaluate(packet,vals,['A0','A1','N'],4)
        require(all(v in (0,1) for v in residuals.values()), 'square-mod-four condition')
        mod4+=1
    return {'actual_tuple_modular_evaluations':count,'mod_four_positive_assignments':mod4,
            'diagnostics_are_not_consistency_tests':True}

def pell_pair(base, index):
    chi,psi=1,0
    for _ in range(index):
        chi,psi=base*chi+(base*base-1)*psi,chi+base*psi
    return chi,psi

def local_positive_examples():
    examples=0; zero_exclusions=0
    for A in [4,5,7]:
        Delta=A*A-1
        for m in [1,2,3,4]:
            f,I=pell_pair(A,m); M=Delta*I
            for R in [5,7,9]:
                chi,y=pell_pair(M,R)
                require(chi%M==0,'odd Pell quotient')
                V=chi//M; gap=y-V
                require(gap>=8*M*M-4,'canonical positive gap')
                f0=A*I; n=f-f0+gap
                require(n>0,'positive n')
                D=1+Delta*I*I; Q=M*M; d=Q-1; e=1-I*I
                x=n+f0+V; B=2*d*x
                H=d*(n*n+2*V*n+e)-V*V+1
                N=H*H+2*B*f0*H-B*B*e
                require(N==0 and B!=0,'canonical norm witness')
                require((H+B*f0)%B==0 and (H+B*f0)//B==f,'inverse f')
                require(x-f==y and y-V>0,'inverse y/u')
                examples+=1
    for A in range(4,9):
        Delta=A*A-1
        for I in range(1,7):
            for n in range(1,5):
                D=1+Delta*I*I; Q=Delta*Delta*I*I; V=-n-A*I
                H=(Q-1)*(n*n+2*V*n+1-I*I)-V*V+1
                require(H!=0,'B-zero diagnostic')
                zero_exclusions+=1
    return {'canonical_abstract_pell_examples':examples,
            'B_zero_exclusion_examples':zero_exclusions,
            'scope':'local elimination only; not complete compiler or refutation witnesses'}

def malformed_controls(packet):
    mutants=[]
    m=deepcopy(packet);m['source'][0][2]=True;mutants.append(m)
    m=deepcopy(packet);m['source'][0][2]='not_a_leaf';mutants.append(m)
    m=deepcopy(packet);m['source'][0][1]='/';mutants.append(m)
    m=deepcopy(packet);m['operations']+=1;mutants.append(m)
    m=deepcopy(packet);m['source'][-1][0]=m['source'][0][0];mutants.append(m)
    for mutant in mutants:
        try: schema(mutant)
        except ValueError: continue
        raise ValueError('a malformed control was accepted')
    return len(mutants)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args(); root=args.root.resolve()
    fixed,coefficient_evidence=coefficients(root)
    receipts=[]
    paths=sorted((root/'circuits').glob('positive12*.json'))
    require(bool(paths),'no twelve-variable circuits')
    for path in paths:
        packet=json.loads(path.read_text())
        graph=schema(packet)
        ring,v,l0,l1,lN,outer=check_exact_outer(packet)
        norm=check_norm_cut(packet)
        finalizer=check_finalizer(packet,ring,l0,l1,lN)
        numeric=modular_checks(packet,fixed)
        receipts.append({'file':str(path.relative_to(root)),
                         'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                         'graph':graph,'outer':outer,'norm':norm,'finalizer':finalizer,
                         'numeric':numeric,'malformed_controls_rejected':malformed_controls(packet)})
    result={'status':'PASS','checker':'independent centered12 stdlib checker',
            'builder_imported':False,'upstream_programs_executed':False,
            'coefficient_payloads':coefficient_evidence,
            'local_examples':local_positive_examples(),'circuits':receipts,
            'proof_boundary':'Finite algebra, exact degree and graph/data checks; the unbounded semantic equivalence uses the written proof and named inherited compiler/Pell results.'}
    payload=json.dumps(result,indent=2)+'\n'
    if args.output: args.output.write_text(payload)
    print(payload)

if __name__=='__main__': main()
