#!/usr/bin/env python3
"""Fresh fixed-size integer-polynomial source for five-signal validity.

No source imports, upstream executables, physical trajectories, saved programs,
or input-dependent source loops. POWER's 15 equations are written out here.
The JSON DAGs are authoritative; aliases are not new leaves or free arithmetic.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


class Term:
    def __init__(self, owner, ref):
        self.owner, self.ref = owner, ref
    def __add__(self, other): return self.owner.op('+', self, other)
    def __radd__(self, other): return self.owner.op('+', other, self)
    def __sub__(self, other): return self.owner.op('-', self, other)
    def __rsub__(self, other): return self.owner.op('-', other, self)
    def __mul__(self, other): return self.owner.op('*', self, other)
    def __rmul__(self, other): return self.owner.op('*', other, self)


class Source:
    def __init__(self, input_names):
        self.inputs = list(input_names)
        self.witnesses, self.gates, self.equations, self.regions = [], [], [], []
        self.ports, self.modules = {}, []
        self.region_name = None
        self.region_start = None
    def term(self, value):
        if isinstance(value, Term):
            require(value.owner is self, 'mixed sources')
            return value
        require(type(value) is int, 'noninteger coefficient')
        return Term(self, 'c:' + str(value))
    def inp(self, name):
        require(name in self.inputs, 'unknown input')
        return Term(self, 'i:' + name)
    def pos(self, name):
        require(name not in self.witnesses, 'duplicate witness')
        self.witnesses.append(name)
        return Term(self, 'w:' + name)
    def nat(self, name):
        return self.pos(name + '.Plus') - 1
    def signed(self, name):
        # p-m = (p-1)-(m-1); no artificial uniqueness or sign test.
        return self.pos(name + '.Positive') - self.pos(name + '.Negative')
    def op(self, op, left, right):
        require(op in ('+', '-', '*'), 'invalid gate')
        self.gates.append([op, self.term(left).ref, self.term(right).ref])
        return Term(self, 'g:' + str(len(self.gates) - 1))
    def eq(self, name, left, right):
        require(name not in [e[0] for e in self.equations], 'duplicate residual')
        self.equations.append([name, self.term(left).ref, self.term(right).ref])
    def region(self, name):
        end = (len(self.witnesses), len(self.gates), len(self.equations))
        if self.region_name is not None:
            self.regions.append(dict(name=self.region_name,
                                     witness_range=[self.region_start[0], end[0]],
                                     gate_range=[self.region_start[1], end[1]],
                                     equation_range=[self.region_start[2], end[2]]))
        self.region_name, self.region_start = name, end
    def alias(self, **ports):
        self.ports.update({name:self.term(value).ref for name,value in ports.items()})
    def power(self, base, exponent, prefix):
        b, n = self.term(base), self.term(exponent)
        z = self.pos(prefix + '.out')
        a = self.pos(prefix + '.aMinus1') + 1
        beta = self.pos(prefix + '.betaMinus1') + 1
        p = {key:self.pos(prefix + '.' + key) for key in
             ('w','M','g','x','y','u','v','s','t','qb','qv','strict')}
        d = {key:self.nat(prefix + '.' + key) for key in
             ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2',
              'tau1','tau2','rho1','rho2')}
        w,M,g,x,y,u,v,s,t,qb,qv,strict = [p[key] for key in
             ('w','M','g','x','y','u','v','s','t','qb','qv','strict')]
        k, m = n+1, b*z
        aa, yy, bb, foury = a*a, y*y, beta*beta, 4*y
        dlt, wp, wg = aa-1, w+1, w*g
        equations = [
          (x*x, 1+dlt*yy),
          (u*u, 1+dlt*(v*v)),
          (s*s, 1+(bb-1)*(t*t)),
          (beta, 1+foury*qb),
          (beta+u*d['alpha1'], a+u*d['alpha2']),
          (v, yy*qv),
          (s+u*d['sigma1'], x+u*d['sigma2']),
          (t+foury*d['tau1'], k+foury*d['tau2']),
          (y, k+d['dyk']),
          (w, b+d['dwb']),
          (w, k+d['dwk']),
          (M, m+strict),
          (aa, 1+(wp*wp-1)*(wg*wg)),
          (2*a*b, M+(b*b+1)),
          (x+M*d['rho1'], y*(a-b)+m+M*d['rho2'])]
        for j,(left,right) in enumerate(equations,1):
            self.eq(prefix+'.eq'+str(j),left,right)
        self.modules.append(dict(name=prefix,kind='POWER',base=b.ref,
                                 exponent=n.ref,out=z.ref))
        return z
    def finish(self, variant):
        self.region('sum_of_squares')
        body_gate_count = len(self.gates)
        squared = []
        for _,left,right in self.equations:
            residual = Term(self,left)-Term(self,right)
            squared.append(residual*residual)
        output = squared[0]
        for sq in squared[1:]:
            output = output + sq
        self.region(None)
        return dict(schema='fixed-positive-integer-polynomial-dag-v1',
                    variant=variant,inputs=self.inputs,witnesses=self.witnesses,
                    domain='Every input and every witness leaf is an ordinary strictly positive integer.',
                    constants='Fixed integer literals are free. Each displayed binary +, -, * gate is charged.',
                    gates=self.gates,equations=self.equations,regions=self.regions,
                    ports=self.ports,modules=self.modules,output=output.ref,
                    body_gate_count=body_gate_count)


def construct(one_input=False, quartic=False):
    S = Source(['code'] if one_input else ['g1','g2','g3'])
    S.region('input_decode')
    if one_input:
        g1,g2,g3 = [S.pos('gap.'+str(j)) for j in (1,2,3)]
        inner = S.nat('decode.inner')
        a,b,c = g1-1,g2-1,g3-1
        bc = b+c
        S.eq('decode.inner_cantor',2*inner,bc*(bc+1)+2*c)
        ai = a+inner
        S.eq('decode.outer_cantor',2*(S.inp('code')-1),ai*(ai+1)+2*inner)
        S.alias(inner_code=inner)
    else:
        g1,g2,g3 = [S.inp('g'+str(j)) for j in (1,2,3)]
    S.alias(g1=g1,g2=g2,g3=g3)
    S.region('radius')
    D = g1+g2+g3
    x,y = g1,g1+g2
    A,B = 3*x-D,3*y-2*D
    delta = S.nat('radius.delta')
    S.eq('radius.nonnegative',4*(D*D),205*(A*A+B*B)+delta)
    U,V = 6*A-13*B,13*A+6*B
    S.alias(D=D,x=x,y=y,A=A,B=B,delta=delta,U=U,V=V)
    S.region('primitive_gaussian_fraction')
    h,q = S.pos('fraction.h'),S.pos('fraction.q')
    u,v = S.signed('fraction.u'),S.signed('fraction.v')
    c1,c2,c3 = [S.signed('bezout.'+str(j)) for j in (1,2,3)]
    S.eq('fraction.real',U,h*u)
    S.eq('fraction.imag',V,h*v)
    S.eq('fraction.denominator',2*D,h*q)
    S.eq('fraction.primitive',c1*u+c2*v+c3*q,1)
    S.alias(h=h,q=q,u=u,v=v,bezout1=c1,bezout2=c2,bezout3=c3)
    S.region('valuation_exponent')
    n = S.nat('valuation.n')
    S.region('power5')
    P = S.power(5,n,'power5')
    S.region('valuation')
    r = S.pos('valuation.r')
    k = S.nat('valuation.k')
    s = S.pos('valuation.s')
    S.eq('valuation.decompose',q,P*r)
    S.eq('valuation.remainder',r,5*k+s)
    if quartic:
        S.eq('valuation.nonzero_remainder',(s-1)*(s-2)*(s-3)*(s-4),0)
    else:
        t = S.pos('valuation.t')
        S.eq('valuation.nonzero_remainder',s+t,5)
        S.alias(remainder_complement=t)
    S.alias(n=n,P=P,r=r,k=k,s=s)
    S.region('extraction_base')
    b = 4*P+1
    Bexp = 3+4*b
    S.alias(radix=b,power_base=Bexp)
    S.region('power_complex')
    T = S.power(Bexp,n,'power_complex')
    S.region('bounded_complex_remainder')
    C,Sine = S.signed('complex.C'),S.signed('complex.S')
    slack = [S.nat('complex.bound.'+str(j)) for j in (1,2,3,4)]
    S.eq('complex.C_lower',C+P,slack[0])
    S.eq('complex.C_upper',P-C,slack[1])
    S.eq('complex.S_lower',Sine+P,slack[2])
    S.eq('complex.S_upper',P-Sine,slack[3])
    kap = S.signed('complex.quotient')
    S.eq('complex.remainder',T-C-b*Sine,kap*(b*b+1))
    S.alias(T=T,C=C,S=Sine,kappa=kap)
    S.region('acceptance')
    dr,du,dv = r-1,u-C,v+Sine
    positive = S.pos('acceptance.positive')
    S.eq('acceptance.strict',delta*delta+dr*dr+du*du+dv*dv,positive)
    S.alias(acceptance_positive=positive)
    return S.finish(('one-input' if one_input else 'three-input')+
                    ('-quartic' if quartic else '-linear'))


def audit_source(dag):
    degrees = {'i:'+n:1 for n in dag['inputs']}
    degrees.update({'w:'+n:1 for n in dag['witnesses']})
    def degree(ref): return 0 if ref.startswith('c:') else degrees[ref]
    for j,(op,a,b) in enumerate(dag['gates']):
        da,db = degree(a),degree(b)
        degrees['g:'+str(j)] = da+db if op=='*' else max(da,db)
    live,pending = set(),[dag['output']]
    while pending:
        ref=pending.pop()
        if ref in live: continue
        live.add(ref)
        if ref.startswith('g:'):
            pending.extend(dag['gates'][int(ref[2:])][1:])
    required = (['g:'+str(j) for j in range(len(dag['gates']))]+
                ['i:'+n for n in dag['inputs']]+['w:'+n for n in dag['witnesses']])
    require(all(ref in live for ref in required), 'dead gate/input/witness')
    reg=[]
    for region in dag['regions']:
        w0,w1=region['witness_range']; g0,g1=region['gate_range']; e0,e1=region['equation_range']
        reg.append(dict(name=region['name'],witnesses=w1-w0,equations=e1-e0,
                        gates=g1-g0,operations=dict(Counter(g[0] for g in dag['gates'][g0:g1]))))
    return dict(variant=dag['variant'],inputs=len(dag['inputs']),
                positive_witnesses=len(dag['witnesses']),equations=len(dag['equations']),
                gates=len(dag['gates']),body_gates=dag['body_gate_count'],
                operations=dict(Counter(g[0] for g in dag['gates'])),regions=reg,
                syntactic_degree_upper_bound=degree(dag['output']),
                residual_degree_upper_bounds={n:max(degree(a),degree(b)) for n,a,b in dag['equations']},
                POWER_calls=len(dag['modules']),dead_gates=0,dead_witnesses=0,dead_inputs=0)


def main():
    target=HERE/'evidence'; target.mkdir(exist_ok=True)
    receipts=[]
    for one_input,quartic in ((False,False),(True,False),(False,True),(True,True)):
        dag=construct(one_input,quartic)
        raw=(json.dumps(dag,sort_keys=True,separators=(',',':'))+'\n').encode()
        receipt=audit_source(dag)
        receipt['dag_sha256']=hashlib.sha256(raw).hexdigest()
        receipt['emitter_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        (target/(dag['variant']+'.dag.json')).write_bytes(raw)
        (target/(dag['variant']+'.receipt.json')).write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
        receipts.append({key:receipt[key] for key in ('variant','inputs','positive_witnesses','equations','gates','operations','syntactic_degree_upper_bound','dag_sha256')})
    (target/'summary.json').write_text(json.dumps(receipts,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipts,sort_keys=True,indent=2))


if __name__=='__main__':
    main()
