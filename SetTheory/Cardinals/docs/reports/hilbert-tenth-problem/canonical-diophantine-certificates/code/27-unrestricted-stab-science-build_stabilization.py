#!/usr/bin/env python3
"""New fixed-shape expanded polynomial for unrestricted finite stabilization.

This source imports only the standard library. No inherited builder, simulator,
checker, universal-machine schedule, or theorem prover is run. All construction
loops are over fixed finite syntax, never over any mathematical input value.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


class Expr:
    def __init__(self, owner, ref): self.owner, self.ref = owner, ref
    def __add__(self, other): return self.owner.gate('+', self, other)
    def __radd__(self, other): return self.owner.gate('+', other, self)
    def __sub__(self, other): return self.owner.gate('-', self, other)
    def __rsub__(self, other): return self.owner.gate('-', other, self)
    def __mul__(self, other): return self.owner.gate('*', self, other)
    def __rmul__(self, other): return self.owner.gate('*', other, self)


class Source:
    def __init__(self):
        self.witnesses, self.gates, self.equalities, self.macros = [], [], [], []
        self.names, self.eq_names, self.ports = set(), set(), {}
        self.input = Expr(self, 'input:InputPlus')
    def expr(self, value):
        if isinstance(value, Expr):
            if value.owner is not self: raise ValueError('foreign expression')
            return value
        if type(value) is not int: raise TypeError('integer literal required')
        return Expr(self, 'constant:' + str(value))
    def gate(self, operation, left, right):
        if operation not in ('+', '-', '*'): raise ValueError(operation)
        a, b = self.expr(left), self.expr(right)
        index = len(self.gates)
        self.gates.append([operation, a.ref, b.ref])
        return Expr(self, 'gate:' + str(index))
    def positive(self, name):
        if name in self.names: raise ValueError('duplicate witness ' + name)
        self.names.add(name)
        self.witnesses.append(name)
        return Expr(self, 'witness:' + name)
    def natural(self, name): return self.positive(name + '.Plus') - 1
    def equation(self, name, left, right):
        if name in self.eq_names: raise ValueError('duplicate equality ' + name)
        self.eq_names.add(name)
        self.equalities.append([self.expr(left).ref, self.expr(right).ref, name])
    def log(self, kind, name, **ports):
        self.macros.append({'kind':kind, 'name':name,
                            **{k:self.expr(v).ref for k,v in ports.items()}})
    def power(self, base, exponent, name):
        b, n = self.expr(base), self.expr(exponent)
        out = self.positive(name + '.out')
        a, beta = self.positive(name + '.aMinus1') + 1, self.positive(name + '.betaMinus1') + 1
        pp = {k:self.positive(name + '.' + k) for k in
              ('w','M','g','x','y','u','v','s','t','qb','qv','strict')}
        nn = {k:self.natural(name + '.' + k) for k in
              ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2',
               'tau1','tau2','rho1','rho2')}
        w,M,g,x,y,u,v,s,t,qb,qv,strict = [pp[k] for k in
              ('w','M','g','x','y','u','v','s','t','qb','qv','strict')]
        k, m = n + 1, b * out
        aa, yy, bb, fy = a*a, y*y, beta*beta, 4*y
        delta, wp, wg = aa-1, w+1, w*g
        clauses = (
            (x*x, 1+delta*yy),
            (u*u, 1+delta*(v*v)),
            (s*s, 1+(bb-1)*(t*t)),
            (beta, 1+fy*qb),
            (beta+u*nn['alpha1'], a+u*nn['alpha2']),
            (v, yy*qv),
            (s+u*nn['sigma1'], x+u*nn['sigma2']),
            (t+fy*nn['tau1'], k+fy*nn['tau2']),
            (y, k+nn['dyk']),
            (w, b+nn['dwb']),
            (w, k+nn['dwk']),
            (M, m+strict),
            (aa, 1+(wp*wp-1)*(wg*wg)),
            (2*a*b, M+(b*b+1)),
            (x+M*nn['rho1'], y*(a-b)+m+M*nn['rho2']),
        )
        for j,(left,right) in enumerate(clauses,1):
            self.equation(name+'.eq'+str(j), left, right)
        self.log('power', name, base=b, exponent=n, out=out)
        return out
    def geom(self, base, length, name):
        b,n = self.expr(base), self.expr(length)
        end = self.power(b,n,name+'.power')
        value = self.natural(name+'.value')
        self.equation(name+'.geometric',(b-1)*value+1,end)
        self.log('geometric',name,base=b,length=n,out=value)
        return value
    def subset(self, mask, value, name):
        M,U = self.expr(mask), self.expr(value)
        ell = self.power(2,M+1,name+'.radix')
        position = self.power(ell,U,name+'.position')
        expansion = self.power(ell+1,M,name+'.expansion')
        q,h,r = [self.natural(name+'.'+v) for v in ('quotient','half','remainder')]
        ds,rs = [self.positive(name+'.'+v) for v in ('digitSlack','remainderSlack')]
        odd = 2*h+1
        self.equation(name+'.extract',expansion,(q*ell+odd)*position+r)
        self.equation(name+'.digitBound',odd+ds,ell)
        self.equation(name+'.remainderBound',r+rs,position)
        self.log('subset',name,mask=M,value=U)
    def bitand(self, left, right, name):
        X,Y = self.expr(left),self.expr(right)
        W,A,C = [self.natural(name+'.'+s) for s in ('common','leftOnly','rightOnly')]
        self.equation(name+'.partitionLeft',X,W+A)
        self.equation(name+'.partitionRight',Y,W+C)
        self.subset(X,W,name+'.left')
        self.subset(Y,W,name+'.right')
        self.subset(A+C,A,name+'.disjoint')
        self.log('and',name,left=X,right=Y,out=W)
        return W
    def spread(self, value, base, length, stride, name):
        U,b,n,s = [self.expr(z) for z in (value,base,length,stride)]
        gap,strict = self.natural(name+'.strideGap'),self.positive(name+'.rangeSlack')
        self.equation(name+'.strideBound',s,n+1+gap)
        limit = self.power(b,n,name+'.range')
        self.equation(name+'.rangeBound',U+strict,limit)
        copybase = self.power(b,s-1,name+'.copyBase')
        copyend = self.power(copybase,n,name+'.copyEnd')
        copying,masking = self.natural(name+'.copying'),self.natural(name+'.masking')
        self.equation(name+'.copyGeom',(copybase-1)*copying+1,copyend)
        self.equation(name+'.maskGeom',(b*copybase-1)*masking+1,copyend*limit)
        out = self.bitand(U*copying,(b-1)*masking,name+'.select')
        self.log('spread',name,value=U,base=b,length=n,stride=s,out=out)
        return out
    def stable(self, mask, name, input_stream=None):
        bits = [self.natural(name+'.bit'+str(i)) for i in range(3)]
        for i in range(3): self.subset(mask,bits[i],name+'.allow'+str(i))
        self.subset(mask,bits[1]+bits[2],name+'.exclude67')
        stream = bits[0]+2*bits[1]+4*bits[2]
        if input_stream is not None: self.equation(name+'.reconstruct',input_stream,stream)
        self.log('stable',name,mask=mask,out=stream)
        return stream
    def finish(self):
        body = len(self.gates)
        summands = []
        for left,right,_ in self.equalities:
            residual = Expr(self,left)-Expr(self,right)
            summands.append(residual*residual)
        total = summands[0]
        for term in summands[1:]: total = total+term
        return {'schema':'fixed-positive-integer-polynomial-dag-v1',
                'input':'InputPlus','domain':'InputPlus and every witness are strictly positive integers',
                'constants':'Fixed integer literals are free; every binary +,-,* gate is counted',
                'witnesses':self.witnesses,'gates':self.gates,'equalities':self.equalities,
                'macros':self.macros,'ports':self.ports,'body_gate_count':body,'output':total.ref}


def construct():
    s = Source()
    p,q,r,d,e,f = [s.positive('descriptor.'+axis) for axis in ('p','q','r','d','e','f')]
    tile,patch = s.natural('descriptor.tile'),s.natural('descriptor.patch')
    fields = (p-1,q-1,r-1,tile,d-1,e-1,f-1,patch)
    suffix = fields[-1]
    for j in range(6,-1,-1):
        encoded = s.input-1 if j==0 else s.natural('descriptor.pair'+str(j))
        total = fields[j]+suffix
        s.equation('descriptor.cantor'+str(j),2*encoded,total*(total+1)+2*suffix)
        suffix = encoded

    tile_size,patch_size = p*q*r,d*e*f
    tile_mask = s.geom(32,tile_size,'tile.externalMask')
    s.stable(tile_mask,'tile.externalDigits',tile)
    patch_mask = s.geom(32,patch_size,'patch.externalMask')
    s.subset(15*patch_mask,patch,'patch.externalDigits')

    # Precision and both conversions are witnesses, with fully paid arithmetic.
    precision = s.positive('radix.precision')
    radix = s.power(32,precision,'radix.base')
    sixteenth = s.positive('radix.sixteenth')
    s.equation('radix.sixteenthEquation',16*sixteenth,radix)
    tile_wide = s.spread(tile,32,tile_size,precision,'tile.convert')
    patch_wide = s.spread(patch,32,patch_size,precision,'patch.convert')

    tx,ty,tz = [s.positive('box.t'+axis)+1 for axis in ('x','y','z')]
    hx,hy,hz = p*d*tx,q*e*ty,r*f*tz
    A,B,C = 2*hx,2*hy,2*hz
    AB = A*B
    tile_sx,tile_sy,tile_sz = 2*d*tx,2*e*ty,2*f*tz
    patch_sx,patch_sy = 2*p*tx,2*q*ty
    tile_row = s.power(radix,p,'tile.rowBase')
    tile_rows = s.spread(tile_wide,tile_row,q*r,tile_sx,'tile.rows')
    tile_plane = s.power(radix,A*q,'tile.planeBase')
    tile_embedded = s.spread(tile_rows,tile_plane,r,tile_sy,'tile.planes')
    repeat_x = s.geom(tile_row,tile_sx,'tile.repeatX')
    repeat_y = s.geom(tile_plane,tile_sy,'tile.repeatY')
    tile_z = s.power(radix,AB*r,'tile.zBase')
    repeat_z = s.geom(tile_z,tile_sz,'tile.repeatZ')
    background = tile_embedded*repeat_x*repeat_y*repeat_z
    patch_row = s.power(radix,d,'patch.rowBase')
    patch_rows = s.spread(patch_wide,patch_row,e*f,patch_sx,'patch.rows')
    patch_plane = s.power(radix,A*e,'patch.planeBase')
    patch_embedded = s.spread(patch_rows,patch_plane,f,patch_sy,'patch.planes')
    patch_shift = s.power(radix,hx+A*hy+AB*hz,'patch.shift')
    additions = patch_embedded*patch_shift

    X = s.power(radix,A,'box.X')
    Y = s.power(X,B,'box.Y')
    Q = s.power(Y,C,'box.Q')
    J = s.natural('box.J')
    s.equation('box.JEquation',(radix-1)*J+1,Q)
    jx,jy,jz = [s.natural('box.j'+axis) for axis in ('x','y','z')]
    s.equation('box.jxEquation',radix*radix*((radix-1)*jx+1),X)
    s.equation('box.jyEquation',X*X*((X-1)*jy+1),Y)
    s.equation('box.jzEquation',Y*Y*((Y-1)*jz+1),Q)
    interior = radix*X*Y*jx*jy*jz
    capacity = sixteenth-1
    U = s.natural('supersolution.U')
    s.subset(capacity*interior,U,'supersolution.support')
    nx,ny,nz = [s.natural('supersolution.negative'+axis) for axis in ('x','y','z')]
    s.equation('supersolution.divX',radix*nx,U)
    s.equation('supersolution.divY',X*ny,U)
    s.equation('supersolution.divZ',Y*nz,U)
    endpoint = s.stable(J,'endpoint')
    left = background+additions+radix*U+X*U+Y*U+nx+ny+nz
    right = 6*U+endpoint
    s.equation('sandpile.balance',left,right)

    ports = dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=tile,patch=patch,
                 tile_size=tile_size,patch_size=patch_size,precision=precision,
                 radix=radix,sixteenth=sixteenth,capacity=capacity,
                 tile_converted=tile_wide,patch_converted=patch_wide,
                 half_x=hx,half_y=hy,half_z=hz,A=A,B=B,C=C,X=X,Y=Y,Q=Q,
                 background=background,additions=additions,all_slots=J,
                 interior_mask=interior,supersolution=U,endpoint=endpoint,
                 balance_left=left,balance_right=right)
    s.ports = {name:s.expr(value).ref for name,value in ports.items()}
    return s.finish()


def inspect(dag):
    degree = {'input:InputPlus':1,**{'witness:'+name:1 for name in dag['witnesses']}}
    def deg(ref): return 0 if ref.startswith('constant:') else degree[ref]
    for j,(op,a,b) in enumerate(dag['gates']):
        if op not in ('+','-','*'): raise ValueError('nonpolynomial gate')
        degree['gate:'+str(j)] = deg(a)+deg(b) if op=='*' else max(deg(a),deg(b))
    live, pending = set(), [dag['output']]
    while pending:
        ref = pending.pop()
        if ref in live: continue
        live.add(ref)
        if ref.startswith('gate:'): pending.extend(dag['gates'][int(ref[5:])][1:])
    dead_gates = [j for j in range(len(dag['gates'])) if 'gate:'+str(j) not in live]
    dead_witnesses = [name for name in dag['witnesses'] if 'witness:'+name not in live]
    if dead_gates or dead_witnesses: raise ValueError('dead source objects')
    count = lambda gs: dict(Counter(g[0] for g in gs))
    body = dag['body_gate_count']
    return dict(positive_witnesses=len(dag['witnesses']),equalities=len(dag['equalities']),
                gates=len(dag['gates']),body_counts=count(dag['gates'][:body]),
                sos_counts=count(dag['gates'][body:]),full_counts=count(dag['gates']),
                macro_calls=dict(Counter(m['kind'] for m in dag['macros'])),
                degree_upper_bound=deg(dag['output']),dead_gates=dead_gates,
                dead_witnesses=dead_witnesses,ports=len(dag['ports']))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'evidence')
    args=parser.parse_args()
    dag=construct()
    receipt=inspect(dag)
    encoded=(json.dumps(dag,sort_keys=True,separators=(',',':'))+'\n').encode()
    receipt['dag_sha256']=hashlib.sha256(encoded).hexdigest()
    receipt['builder_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'polynomial-dag.json').write_bytes(encoded)
    (args.output/'build-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))


if __name__=='__main__': main()
