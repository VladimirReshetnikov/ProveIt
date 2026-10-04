#!/usr/bin/env python3
"""Newly authored fixed-shape integer-polynomial source builder; no upstream imports.

The only output is a +,-,* DAG and a receipt. Dimensions are witness values,
never Python loop bounds. All quantified variables are strictly positive.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


class E:
    def __init__(self, b, ref): self.b, self.ref = b, ref
    def __add__(self, x): return self.b.op('+', self, x)
    def __radd__(self, x): return self.b.op('+', x, self)
    def __sub__(self, x): return self.b.op('-', self, x)
    def __rsub__(self, x): return self.b.op('-', x, self)
    def __mul__(self, x): return self.b.op('*', self, x)
    def __rmul__(self, x): return self.b.op('*', x, self)


class Builder:
    def __init__(self):
        self.gates, self.witnesses, self.equalities, self.macros = [], [], [], []
        self.names, self.ports = set(), {}
        self.input = E(self, 'input:InputPlus')
    def coerce(self, x):
        if isinstance(x, E):
            if x.b is not self: raise ValueError('mixed builders')
            return x
        if type(x) is not int: raise TypeError(type(x))
        return E(self, 'constant:' + str(x))
    def op(self, op, x, y):
        x, y = self.coerce(x), self.coerce(y)
        ref = 'gate:' + str(len(self.gates))
        self.gates.append([op, x.ref, y.ref])
        return E(self, ref)
    def pos(self, name):
        if name in self.names: raise ValueError('duplicate witness ' + name)
        self.names.add(name); self.witnesses.append(name)
        return E(self, 'witness:' + name)
    def nat(self, name): return self.pos(name + '.Plus') - 1
    def eq(self, x, y, name):
        self.equalities.append([self.coerce(x).ref, self.coerce(y).ref, name])
    def port(self, name, x): self.ports[name] = self.coerce(x).ref
    def power(self, base, exponent, name):
        base, exponent = self.coerce(base), self.coerce(exponent)
        out = self.pos(name + '.out')
        k, m = exponent + 1, base * out
        w = self.pos(name+'.w'); a = self.pos(name+'.A0') + 1
        mod = self.pos(name+'.mod'); g = self.pos(name+'.g')
        x = self.pos(name+'.x'); y = self.pos(name+'.y')
        u = self.pos(name+'.u'); v = self.pos(name+'.v')
        s = self.pos(name+'.s'); t = self.pos(name+'.t')
        beta = self.pos(name+'.B0') + 1
        dwb = self.nat(name+'.dwb'); dwk = self.nat(name+'.dwk')
        dyk = self.nat(name+'.dyk'); slack = self.pos(name+'.S')
        qb = self.pos(name+'.qb'); qv = self.pos(name+'.qv')
        aa = self.nat(name+'.alpha1'); ab = self.nat(name+'.alpha2')
        sa = self.nat(name+'.sigma1'); sb = self.nat(name+'.sigma2')
        ta = self.nat(name+'.tau1'); tb = self.nat(name+'.tau2')
        ra = self.nat(name+'.rho1'); rb = self.nat(name+'.rho2')
        a2, y2, beta2, foury = a*a, y*y, beta*beta, 4*y
        delta = a2 - 1
        eqs = [
            (x*x, 1+delta*y2),
            (u*u, 1+delta*(v*v)),
            (s*s, 1+(beta2-1)*(t*t)),
            (beta, 1+foury*qb),
            (beta+u*aa, a+u*ab),
            (v, y2*qv),
            (s+u*sa, x+u*sb),
            (t+foury*ta, k+foury*tb),
            (y, k+dyk), (w, base+dwb), (w, k+dwk),
            (mod, m+slack),
        ]
        wp, wg = w+1, w*g
        eqs.extend([
            (a2, 1+(wp*wp-1)*(wg*wg)),
            (2*(a*base), mod+(base*base+1)),
            (x+mod*ra, y*(a-base)+m+mod*rb),
        ])
        for i, (left,right) in enumerate(eqs, 1): self.eq(left,right,name+'.eq'+str(i))
        self.macros.append({'kind':'power','name':name,'base':base.ref,'exponent':exponent.ref,'out':out.ref})
        return out
    def geometric(self, base, n, name):
        power = self.power(base,n,name+'.power')
        value = self.nat(name+'.value')
        self.eq((base-1)*value+1,power,name+'.geometric')
        return value
    def subset(self, mask, value, name):
        L = self.power(2,mask+1,name+'.L')
        Y = self.power(L,value,name+'.Y')
        Z = self.power(L+1,mask,name+'.Z')
        q = self.nat(name+'.q'); o = self.nat(name+'.o'); r = self.nat(name+'.r')
        sc = self.pos(name+'.sc'); sr = self.pos(name+'.sr')
        c = 2*o+1
        self.eq(Z,(q*L+c)*Y+r,name+'.extract')
        self.eq(c+sc,L,name+'.digit_bound')
        self.eq(r+sr,Y,name+'.remainder_bound')
        self.macros.append({'kind':'subset','name':name,'mask':mask.ref,'value':value.ref})
    def band(self, x, y, name):
        z, a, c = self.nat(name+'.z'), self.nat(name+'.a'), self.nat(name+'.c')
        self.eq(x,z+a,name+'.left_partition'); self.eq(y,z+c,name+'.right_partition')
        self.subset(x,z,name+'.left'); self.subset(y,z,name+'.right')
        self.subset(a+c,a,name+'.disjoint')
        self.macros.append({'kind':'and','name':name,'left':x.ref,'right':y.ref,'out':z.ref})
        return z
    def spread(self, value, base, n, stride, name):
        gap, slack = self.nat(name+'.stride_gap'), self.pos(name+'.range_slack')
        self.eq(stride,n+1+gap,name+'.stride_bound')
        P = self.power(base,n,name+'.range_power')
        self.eq(value+slack,P,name+'.range_bound')
        C = self.power(base,stride-1,name+'.copy_base')
        E0 = self.power(C,n,name+'.copy_power')
        DD, FF = base*C, E0*P
        G1, G2 = self.nat(name+'.copy_geometric'), self.nat(name+'.mask_geometric')
        self.eq((C-1)*G1+1,E0,name+'.copy_geometric_eq')
        self.eq((DD-1)*G2+1,FF,name+'.mask_geometric_eq')
        result = self.band(value*G1,(base-1)*G2,name+'.select')
        self.macros.append({'kind':'spread','name':name,'value':value.ref,'base':base.ref,'length':n.ref,'stride':stride.ref,'out':result.ref})
        return result
    def bits05(self, stream, mask, name):
        a,c,d = self.nat(name+'.bit0'),self.nat(name+'.bit1'),self.nat(name+'.bit2')
        self.subset(mask,a,name+'.allow0'); self.subset(mask,c,name+'.allow1')
        self.subset(mask,d,name+'.allow2'); self.subset(mask,c+d,name+'.exclude67')
        value = a+2*c+4*d
        if stream is not None: self.eq(stream,value,name+'.reconstruct')
        return value
    def finish(self):
        squares=[]
        for a,b,name in self.equalities:
            residual = E(self,a)-E(self,b)
            squares.append(residual*residual)
        total=squares[0]
        for square in squares[1:]: total=total+square
        return {'schema':'fixed-positive-integer-polynomial-dag-v1','input':'InputPlus',
                'domain':'InputPlus and every witness are positive integers',
                'constants':'Fixed integer literals are free; every emitted +,-,* gate is counted',
                'witnesses':self.witnesses,'gates':self.gates,'equalities':self.equalities,
                'ports':self.ports,'macros':self.macros,'output':total.ref}


def build():
    b=Builder()
    p,q,r,d,e,f = [b.pos('input.'+s) for s in ('p','q','r','d','e','f')]
    tile,patch=b.nat('input.tile'),b.nat('input.patch')
    fields=[p-1,q-1,r-1,tile,d-1,e-1,f-1,patch]
    paired=fields[-1]
    for j in range(6,-1,-1):
        nxt = b.input-1 if j==0 else b.nat('input.pair'+str(j))
        sm=fields[j]+paired
        b.eq(2*nxt,sm*(sm+1)+2*paired,'input.cantor'+str(j))
        paired=nxt
    tx,ty,tz=[b.pos('box.t'+s)+1 for s in ('x','y','z')]
    ax,ay,az=p*d*tx,q*e*ty,r*f*tz
    A,B,C=2*ax,2*ay,2*az
    AB=A*B
    sx_tile,sx_patch,sy_tile,sy_patch=2*d*tx,2*p*tx,2*e*ty,2*q*ty
    sz_tile=2*f*tz
    QR,EF=q*r,e*f
    mask_tile=b.geometric(b.coerce(32),p*QR,'tile.mask')
    b.bits05(tile,mask_tile,'tile.digits')
    mask_patch=b.geometric(b.coerce(32),d*EF,'patch.mask')
    b.subset(15*mask_patch,patch,'patch.digits')
    tile_row_base=b.power(32,p,'tile.row_base')
    tile_rows=b.spread(tile,tile_row_base,QR,sx_tile,'tile.rows')
    tile_plane_base=b.power(32,A*q,'tile.plane_base')
    tile_emb=b.spread(tile_rows,tile_plane_base,r,sy_tile,'tile.planes')
    repeatx=b.geometric(tile_row_base,sx_tile,'tile.repeatx')
    repeaty=b.geometric(tile_plane_base,sy_tile,'tile.repeaty')
    tile_z_base=b.power(32,AB*r,'tile.z_base')
    repeatz=b.geometric(tile_z_base,sz_tile,'tile.repeatz')
    background=tile_emb*repeatx*repeaty*repeatz
    patch_row_base=b.power(32,d,'patch.row_base')
    patch_rows=b.spread(patch,patch_row_base,EF,sx_patch,'patch.rows')
    patch_plane_base=b.power(32,A*e,'patch.plane_base')
    patch_emb=b.spread(patch_rows,patch_plane_base,f,sy_patch,'patch.planes')
    shift=b.power(32,ax+A*ay+AB*az,'patch.shift')
    additions=patch_emb*shift
    X=b.power(32,A,'box.X'); Y=b.power(X,B,'box.Y'); Z=b.power(Y,C,'box.Z')
    J=b.nat('box.J'); b.eq(31*J+1,Z,'box.J_eq')
    Jx,Jy,Jz=[b.nat('box.J'+s) for s in ('x','y','z')]
    b.eq(1024*(31*Jx+1),X,'box.Jx_eq')
    b.eq((X*X)*((X-1)*Jy+1),Y,'box.Jy_eq')
    b.eq((Y*Y)*((Y-1)*Jz+1),Z,'box.Jz_eq')
    interior=32*X*Y*Jx*Jy*Jz
    U=b.nat('odometer.U'); b.subset(interior,U,'odometer.binary_interior')
    Ux,Uy,Uz=[b.nat('odometer.U'+s) for s in ('x','y','z')]
    b.eq(32*Ux,U,'odometer.divx'); b.eq(X*Uy,U,'odometer.divy'); b.eq(Y*Uz,U,'odometer.divz')
    endpoint=b.bits05(None,J,'endpoint')
    b.eq(background+additions+32*U+X*U+Y*U+Ux+Uy+Uz,6*U+endpoint,'sandpile.balance')
    for name,expr in [('p',p),('q',q),('r',r),('d',d),('e',e),('f',f),('tile',tile),('patch',patch),
                      ('A',A),('B',B),('C',C),('background',background),('additions',additions),
                      ('interior_mask',interior),('odometer',U),('endpoint',endpoint)]: b.port(name,expr)
    return b.finish()


def inspect(source):
    refs={'input:InputPlus':1}
    for name in source['witnesses']: refs['witness:'+name]=1
    used=set(); counts=Counter(); degrees={}
    def degree(ref):
        if ref.startswith('constant:'):
            int(ref[9:]); return 0
        if ref not in refs: raise ValueError('undefined reference '+ref)
        return refs[ref]
    for i,(op,left,right) in enumerate(source['gates']):
        if op not in ('+','-','*'): raise ValueError('nonpolynomial gate')
        dl,dr=degree(left),degree(right)
        deg=dl+dr if op=='*' else max(dl,dr)
        refs['gate:'+str(i)]=deg; counts[op]+=1
    reachable=set()
    def visit(start):
        stack=[start]
        while stack:
            ref=stack.pop()
            if ref in reachable: continue
            reachable.add(ref)
            if ref.startswith('gate:'):
                _,left,right=source['gates'][int(ref[5:])];stack.extend([left,right])
    visit(source['output'])
    dead_gates=[i for i in range(len(source['gates'])) if 'gate:'+str(i) not in reachable]
    dead_witnesses=[w for w in source['witnesses'] if 'witness:'+w not in reachable]
    if dead_witnesses: raise ValueError('dead witnesses '+str(dead_witnesses))
    powers=[m for m in source['macros'] if m['kind']=='power']
    macro_counts=Counter(m['kind'] for m in source['macros'])
    return {'positive_witnesses':len(source['witnesses']),'polynomial_equalities':len(source['equalities']),
            'arithmetic_gates':len(source['gates']),'multiplications':counts['*'],
            'additions':counts['+'],'subtractions':counts['-'],
            'degree_upper_bound':degree(source['output']),'dead_gate_indices':dead_gates,
            'dead_witnesses':dead_witnesses,'macro_calls':dict(macro_counts),
            'source_contains_only_polynomial_gates':True,
            'source_shape_independent_of_input':True,
            'proof_scope':'Pell soundness is inherited from the pinned constructive theorem; finite tests do not re-prove it.'}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    source=build(); receipt=inspect(source)
    raw=(json.dumps(source,sort_keys=True,separators=(',',':'))+'\n').encode()
    receipt['polynomial_dag_sha256']=hashlib.sha256(raw).hexdigest()
    receipt['builder_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (args.output/'polynomial-dag.json').write_bytes(raw)
    (args.output/'build-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__': main()
