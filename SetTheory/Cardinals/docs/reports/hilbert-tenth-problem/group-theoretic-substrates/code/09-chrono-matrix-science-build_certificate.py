#!/usr/bin/env python3
"""New literal positive-integer certificate for the pinned countdown system.

Reads the upstream receipt only as inert JSON. Runs/imports no upstream program.
Every emitter loop has a fixed bound determined by the 97 fixed transitions.
The POWER and Sub equations are copied transparently from the approved packet.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
RECEIPT_SHA = 'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    answer = {}
    for key, value in pairs:
        require(key not in answer, 'duplicate JSON key')
        answer[key] = value
    return answer


class Term:
    def __init__(self, source, ref): self.source, self.ref = source, ref
    def __add__(self, other): return self.source.binary('+', self, other)
    def __radd__(self, other): return self.source.binary('+', other, self)
    def __sub__(self, other): return self.source.binary('-', self, other)
    def __rsub__(self, other): return self.source.binary('-', other, self)
    def __mul__(self, other): return self.source.binary('*', self, other)
    def __rmul__(self, other): return self.source.binary('*', other, self)


class Source:
    def __init__(self):
        self.witnesses, self.gates, self.equalities, self.macros = [], [], [], []
        self.witness_names, self.equality_names = set(), set()
        self.input = Term(self, 'input:x')
        self.ports = {}
    def term(self, value):
        if isinstance(value, Term):
            require(value.source is self, 'mixed source')
            return value
        require(type(value) is int, 'noninteger literal')
        return Term(self, 'constant:' + str(value))
    def binary(self, op, left, right):
        require(op in ('+', '-', '*'), 'bad gate')
        self.gates.append([op, self.term(left).ref, self.term(right).ref])
        return Term(self, 'gate:' + str(len(self.gates) - 1))
    def pos(self, name):
        require(name not in self.witness_names, 'duplicate witness')
        self.witness_names.add(name)
        self.witnesses.append(name)
        return Term(self, 'witness:' + name)
    def nat(self, name): return self.pos(name + '.Plus') - 1
    def eq(self, name, left, right):
        require(name not in self.equality_names, 'duplicate equality')
        self.equality_names.add(name)
        self.equalities.append([self.term(left).ref, self.term(right).ref, name])
    def add(self, terms):
        require(bool(terms), 'empty sum')
        value = self.term(terms[0])
        for term in terms[1:]: value = value + term
        return value
    def scale(self, coefficient, term):
        require(type(coefficient) is int and coefficient > 0, 'invalid scale')
        return self.term(term) if coefficient == 1 else coefficient * self.term(term)
    def power(self, base, exponent, name):
        b, n = self.term(base), self.term(exponent)
        out = self.pos(name + '.out')
        a = self.pos(name + '.aMinus1') + 1
        beta = self.pos(name + '.betaMinus1') + 1
        pp = {key:self.pos(name + '.' + key) for key in
              ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')}
        nn = {key:self.nat(name + '.' + key) for key in
              ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2',
               'tau1','tau2','rho1','rho2')}
        w,M,g,x,y,u,v,s,t,qb,qv,strict = [pp[key] for key in
              ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')]
        k, m = n + 1, b * out
        aa, yy, bb, foury = a*a, y*y, beta*beta, 4*y
        delta, wp, wg = aa-1, w+1, w*g
        equations = [
            (x*x,1+delta*yy), (u*u,1+delta*(v*v)),
            (s*s,1+(bb-1)*(t*t)), (beta,1+foury*qb),
            (beta+u*nn['alpha1'],a+u*nn['alpha2']), (v,yy*qv),
            (s+u*nn['sigma1'],x+u*nn['sigma2']),
            (t+foury*nn['tau1'],k+foury*nn['tau2']),
            (y,k+nn['dyk']), (w,b+nn['dwb']), (w,k+nn['dwk']),
            (M,m+strict), (aa,1+(wp*wp-1)*(wg*wg)),
            (2*a*b,M+(b*b+1)),
            (x+M*nn['rho1'],y*(a-b)+m+M*nn['rho2'])]
        for j, (left,right) in enumerate(equations,1): self.eq(name+'.eq'+str(j),left,right)
        self.macros.append(dict(kind='power',name=name,base=b.ref,exponent=n.ref,out=out.ref))
        return out
    def subset(self, mask, value, name):
        M, V = self.term(mask), self.term(value)
        radix = self.power(2,M+1,name+'.radix')
        slot = self.power(radix,V,name+'.slot')
        expansion = self.power(radix+1,M,name+'.binomial')
        q,h,r = [self.nat(name+'.'+key) for key in ('quotient','half','remainder')]
        dg,rg = [self.pos(name+'.'+key) for key in ('digit_gap','remainder_gap')]
        odd = 2*h+1
        self.eq(name+'.extract',expansion,(q*radix+odd)*slot+r)
        self.eq(name+'.digit_bound',odd+dg,radix)
        self.eq(name+'.remainder_bound',r+rg,slot)
        self.macros.append(dict(kind='subset',name=name,mask=M.ref,value=V.ref))
    def finish(self):
        body = len(self.gates)
        squares = []
        for left,right,_ in self.equalities:
            residual = Term(self,left)-Term(self,right)
            squares.append(residual*residual)
        output = self.add(squares)
        return dict(schema='fixed-positive-integer-polynomial-dag-v1',input='x',
                    domain='x and every witness are strictly positive integers',
                    constants='Fixed integer literals are free; every binary arithmetic gate is counted',
                    witnesses=self.witnesses,gates=self.gates,equalities=self.equalities,
                    macros=self.macros,ports=self.ports,output=output.ref,body_gate_count=body)


def coefficients():
    raw = (HERE/'sources/matrix193_countdown_rows.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest() == RECEIPT_SHA, 'receipt byte hash mismatch')
    receipt = json.loads(raw, object_pairs_hook=unique_object,
                         parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    transitions = receipt['transitions']
    require(transitions['count'] == 97 and len(transitions['tiles']) == 96, 'wrong alphabet')
    initial = receipt['initial_state']['X'] + receipt['initial_state']['Y']
    require(initial == [35426321,-19628667,1,0], 'wrong initial state')
    def row_map(K,G):
        require(len(K)==len(G)==4 and all(type(v) is int for v in K+G),'bad matrix')
        require(K[0]*K[3]-K[1]*K[2]==G[0]*G[3]-G[1]*G[2]==1,'not determinant one')
        return [[K[0],K[2],0,0],[K[1],K[3],0,0],
                [0,0,G[0],G[2]],[0,0,G[1],G[3]]]
    maps = [row_map([1,0,0,1], transitions['loader']['Y_matrix'])]
    tile_ids = []
    for tile in transitions['tiles']:
        tile_ids.append(tile['tile_id'])
        maps.append(row_map(tile['K'],tile['G']))
    require(len(set(tile_ids))==96,'duplicate tile identifiers')
    offsets = [[1-sum(row) for row in A] for A in maps]
    threshold = max([128] + [2+sum(abs(a) for a in row)+abs(1-sum(row))
                            for A in maps for row in A])
    C = 1 << (threshold-1).bit_length()
    return dict(initial=initial,maps=maps,offsets=offsets,tile_ids=tile_ids,
                radix_factor=C,radix_threshold=threshold,source_receipt_sha256=RECEIPT_SHA,
                convention='A[output][input] represents the actual row-vector right action')


def construct(data):
    S = Source()
    h,ell = S.pos('time.h'),S.pos('bounds.ell')
    H = S.power(2,ell,'bounds.offset')
    D = 2*H
    b = data['radix_factor']*D
    S.eq('bounds.initial',H,max(abs(v) for v in data['initial'])+S.pos('bounds.initial_gap'))
    S.eq('bounds.input',S.input+S.pos('bounds.input_gap'),D)
    W = S.power(b,h,'time.end_power')
    R = S.nat('time.repetition')
    S.eq('time.repetition_equation',(b-1)*R+1,W)
    E = [S.nat('choice.'+str(i)) for i in range(97)]
    for i in range(97): S.subset(R,E[i],'choice.mask.'+str(i))
    S.eq('choice.one_hot',S.add(E),R)

    Q = [[S.nat('slice.'+str(i)+'.'+str(r)) for r in range(4)] for i in range(97)]
    for i in range(97):
        selected_mask = (D-1)*E[i]
        for r in range(4): S.subset(selected_mask,Q[i][r],'slice.mask.'+str(i)+'.'+str(r))
    U = [S.add([Q[i][r] for i in range(97)]) for r in range(4)]
    V = [S.nat('post.'+str(r)) for r in range(5)]
    full_mask = (D-1)*R
    for r in range(5): S.subset(full_mask,V[r],'post.mask.'+str(r))
    N = S.nat('counter.pre')
    S.subset((D-1)*E[0],N,'counter.loader_mask')
    final = [S.nat('final.'+str(r)) for r in range(4)]
    for r in range(4):
        S.eq('final.bound.'+str(r),final[r]+S.pos('final.gap.'+str(r)),D)
        S.eq('chronology.row.'+str(r),b*V[r]+(H+data['initial'][r]),U[r]+W*final[r])
    S.eq('chronology.counter',b*V[4]+S.input,N)
    S.eq('endpoint.0',final[0],final[2])
    S.eq('endpoint.1',final[1],final[3])

    for r in range(4):
        left,right = [V[r]],[]
        lc,rc = [],[]
        for i in range(97):
            for s in range(4):
                a = data['maps'][i][r][s]
                if a<0: left.append(S.scale(-a,Q[i][s]))
                elif a>0: right.append(S.scale(a,Q[i][s]))
            c = data['offsets'][i][r]
            if c<0: lc.append(S.scale(-c,E[i]))
            elif c>0: rc.append(S.scale(c,E[i]))
        if lc: left.append(H*S.add(lc))
        if rc: right.append(H*S.add(rc))
        S.eq('transition.row.'+str(r),S.add(left),S.add(right))
    S.eq('transition.counter',N,V[4]+E[0])
    ports = dict(duration=h,offset_exponent=ell,offset=H,digit_limit=D,
                 radix=b,end_power=W,repetition=R,counter_pre=N,counter_post=V[4])
    for i in range(97):
        ports['selector.'+str(i)] = E[i]
        for r in range(4): ports['slice.'+str(i)+'.'+str(r)] = Q[i][r]
    for r in range(4):
        ports['pre.'+str(r)],ports['post.'+str(r)],ports['final.'+str(r)] = U[r],V[r],final[r]
    S.ports = {key:S.term(value).ref for key,value in ports.items()}
    return S.finish()


def inspect(dag):
    degrees = {'input:x':1, **{'witness:'+w:1 for w in dag['witnesses']}}
    def degree(ref): return 0 if ref.startswith('constant:') else degrees[ref]
    for j,(op,a,b) in enumerate(dag['gates']):
        da,db = degree(a),degree(b)
        degrees['gate:'+str(j)] = da+db if op=='*' else max(da,db)
    pending,seen = [dag['output']],set()
    while pending:
        ref = pending.pop()
        if ref in seen: continue
        seen.add(ref)
        if ref.startswith('gate:'): pending.extend(dag['gates'][int(ref[5:])][1:])
    require(all('gate:'+str(j) in seen for j in range(len(dag['gates']))),'dead gate')
    require(all('witness:'+w in seen for w in dag['witnesses']),'dead witness')
    require('input:x' in seen,'dead input')
    counts = lambda gs:dict(Counter(g[0] for g in gs))
    body = dag['body_gate_count']
    return dict(positive_witnesses=len(dag['witnesses']),equalities=len(dag['equalities']),
                gates=len(dag['gates']),body_counts=counts(dag['gates'][:body]),
                sos_counts=counts(dag['gates'][body:]),full_counts=counts(dag['gates']),
                macros=dict(Counter(m['kind'] for m in dag['macros'])),
                degree_upper_bound=degree(dag['output']),ports=len(dag['ports']),
                dead_gates=0,dead_witnesses=0)


if __name__=='__main__':
    data = coefficients()
    source = construct(data)
    receipt = inspect(source)
    out = HERE/'evidence'
    out.mkdir(exist_ok=True)
    raw = (json.dumps(source,sort_keys=True,separators=(',',':'))+'\n').encode()
    receipt['dag_sha256'] = hashlib.sha256(raw).hexdigest()
    receipt['builder_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    receipt['source_receipt_sha256'] = RECEIPT_SHA
    receipt['radix_factor'] = data['radix_factor']
    receipt['radix_threshold'] = data['radix_threshold']
    (out/'polynomial-dag.json').write_bytes(raw)
    (out/'build-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    (out/'coefficients.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))
