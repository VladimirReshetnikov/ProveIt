#!/usr/bin/env python3
"""Fresh fixed-shape source for legal binary target firing.

No upstream Python, historical recoder, or arithmetic schedule is imported.
All powers are explicit Pell equation systems. Every source loop has fixed size.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parent


class Expr:
    def __init__(self, owner, ref):
        self.owner, self.ref = owner, ref
    def __add__(self, rhs): return self.owner.gate('+', self, rhs)
    def __radd__(self, lhs): return self.owner.gate('+', lhs, self)
    def __sub__(self, rhs): return self.owner.gate('-', self, rhs)
    def __rsub__(self, lhs): return self.owner.gate('-', lhs, self)
    def __mul__(self, rhs): return self.owner.gate('*', self, rhs)
    def __rmul__(self, lhs): return self.owner.gate('*', lhs, self)


class Source:
    def __init__(self):
        self.witnesses = []
        self.gates = []
        self.equalities = []
        self.macros = []
        self.ports = {}
        self.input = Expr(self, 'input:InputPlus')
    def expr(self, value):
        if isinstance(value, Expr):
            assert value.owner is self
            return value
        assert isinstance(value, int)
        return Expr(self, f'constant:{value}')
    def gate(self, op, lhs, rhs):
        assert op in ['+', '-', '*']
        left, right = self.expr(lhs), self.expr(rhs)
        self.gates.append([op, left.ref, right.ref])
        return Expr(self, f'gate:{len(self.gates)-1}')
    def positive(self, label):
        assert label not in self.witnesses, label
        self.witnesses.append(label)
        return Expr(self, 'witness:' + label)
    def natural(self, label): return self.positive(label + '.Plus') - 1
    def equal(self, label, lhs, rhs):
        assert label not in [e[2] for e in self.equalities], label
        self.equalities.append([self.expr(lhs).ref, self.expr(rhs).ref, label])
    def expose(self, label, expr): self.ports[label] = self.expr(expr).ref
    def power(self, base, exponent, label):
        base, exponent = self.expr(base), self.expr(exponent)
        out = self.positive(label + '.out')
        a = self.positive(label + '.aMinus1') + 1
        beta = self.positive(label + '.betaMinus1') + 1
        pp = {s: self.positive(label + '.' + s) for s in
              ['w','modulus','g','x','y','u','v','s','t','qb','qv','strict']}
        nn = {s: self.natural(label + '.' + s) for s in
              ['dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2']}
        w, modulus, g, x, y, u, v, s, t, qb, qv, strict = [pp[z] for z in
              ['w','modulus','g','x','y','u','v','s','t','qb','qv','strict']]
        k, m = exponent + 1, base*out
        aa, yy, bb, foury = a*a, y*y, beta*beta, 4*y
        delta = aa-1
        wp, wg = w+1, w*g
        clauses = [
            (x*x, 1+delta*yy),
            (u*u, 1+delta*(v*v)),
            (s*s, 1+(bb-1)*(t*t)),
            (beta, 1+foury*qb),
            (beta+u*nn['alpha1'], a+u*nn['alpha2']),
            (v, yy*qv),
            (s+u*nn['sigma1'], x+u*nn['sigma2']),
            (t+foury*nn['tau1'], k+foury*nn['tau2']),
            (y, k+nn['dyk']),
            (w, base+nn['dwb']),
            (w, k+nn['dwk']),
            (modulus, m+strict),
            (aa, 1+(wp*wp-1)*(wg*wg)),
            (2*a*base, modulus+(base*base+1)),
            (x+modulus*nn['rho1'], y*(a-base)+m+modulus*nn['rho2'])]
        for i, (left, right) in enumerate(clauses, 1):
            self.equal(f'{label}.eq{i}', left, right)
        self.macros.append({'kind':'power','name':label,'base':base.ref,
                            'exponent':exponent.ref,'out':out.ref})
        return out
    def geom(self, base, length, label):
        base, length = self.expr(base), self.expr(length)
        result = self.natural(label + '.value')
        limit = self.power(base, length, label + '.power')
        self.equal(label + '.equation', (base-1)*result+1, limit)
        return result
    def subset(self, mask, value, label):
        mask, value = self.expr(mask), self.expr(value)
        radix = self.power(2, mask+1, label + '.radix')
        slot = self.power(radix, value, label + '.slot')
        binomial = self.power(radix+1, mask, label + '.binomial')
        quotient, half, remainder = [self.natural(label+'.'+s) for s in ['quotient','half','remainder']]
        digit_gap, remainder_gap = [self.positive(label+'.'+s) for s in ['digit_gap','remainder_gap']]
        odd = 2*half+1
        self.equal(label+'.extract', binomial, (quotient*radix+odd)*slot+remainder)
        self.equal(label+'.digit_bound', odd+digit_gap, radix)
        self.equal(label+'.remainder_bound', remainder+remainder_gap, slot)
        self.macros.append({'kind':'subset','name':label,'mask':mask.ref,'value':value.ref})
    def intersection(self, left, right, label):
        left, right = self.expr(left), self.expr(right)
        common, a, c = [self.natural(label+'.'+s) for s in ['common','left_only','right_only']]
        self.equal(label+'.left_partition', left, common+a)
        self.equal(label+'.right_partition', right, common+c)
        self.subset(left, common, label+'.left')
        self.subset(right, common, label+'.right')
        self.subset(a+c, a, label+'.disjoint')
        self.macros.append({'kind':'and','name':label,'left':left.ref,'right':right.ref,'out':common.ref})
        return common
    def spread(self, value, base, length, stride, label):
        value, base, length, stride = map(self.expr, [value,base,length,stride])
        gap = self.natural(label+'.stride_gap')
        strict = self.positive(label+'.range_gap')
        self.equal(label+'.stride_bound', stride, length+1+gap)
        limit = self.power(base,length,label+'.range')
        self.equal(label+'.range_bound', value+strict, limit)
        copybase = self.power(base,stride-1,label+'.copybase')
        copylimit = self.power(copybase,length,label+'.copylimit')
        copy, mask = self.natural(label+'.copy'), self.natural(label+'.mask')
        self.equal(label+'.copy_equation', (copybase-1)*copy+1, copylimit)
        self.equal(label+'.mask_equation', (base*copybase-1)*mask+1, copylimit*limit)
        result = self.intersection(value*copy,(base-1)*mask,label+'.select')
        self.macros.append({'kind':'spread','name':label,'value':value.ref,'base':base.ref,
                            'length':length.ref,'stride':stride.ref,'out':result.ref})
        return result
    def combine(self):
        body = len(self.gates)
        squares = []
        for left, right, label in self.equalities:
            residual = Expr(self,left)-Expr(self,right)
            squares.append(residual*residual)
        total = squares[0]
        for term in squares[1:]: total = total+term
        return {'schema':'fixed-positive-integer-polynomial-dag-v1', 'input':'InputPlus',
                'domain':'InputPlus and every witness are positive integers',
                'constants':'Fixed integer literals are free; all binary arithmetic gates counted',
                'witnesses':self.witnesses,'gates':self.gates,'equalities':self.equalities,
                'macros':self.macros,'ports':self.ports,'output':total.ref,'body_gate_count':body}


def construct():
    s = Source()
    p,q,r,d,e,f = [s.positive('descriptor.'+axis) for axis in ['p','q','r','d','e','f']]
    tile, patch = s.natural('descriptor.tile'), s.natural('descriptor.patch')
    zeta = [s.natural('target.zeta'+axis) for axis in ['x','y','z']]
    fields = [p-1,q-1,r-1,tile,d-1,e-1,f-1,patch]+zeta
    rest = fields[-1]
    for j in range(9,-1,-1):
        code = s.input-1 if j==0 else s.natural('descriptor.pair'+str(j))
        combined = fields[j]+rest
        s.equal('descriptor.cantor'+str(j), 2*code, combined*(combined+1)+2*rest)
        rest = code
    tx,ty,tz = [s.positive('box.t'+axis)+1 for axis in ['x','y','z']]
    hx,hy,hz = p*d*tx,q*e*ty,r*f*tz
    A,B,C = 2*hx,2*hy,2*hz
    AB = A*B
    txrep,tyrep,tzrep = 2*d*tx,2*e*ty,2*f*tz
    pxrep,pyrep = 2*p*tx,2*q*ty
    qr,ef = q*r,e*f

    tilemask = s.geom(32,p*qr,'tile.mask')
    tilebits = [s.natural('tile.bit'+str(i)) for i in range(3)]
    for i in range(3): s.subset(tilemask,tilebits[i],'tile.allow'+str(i))
    s.subset(tilemask,tilebits[1]+tilebits[2],'tile.exclude67')
    s.equal('tile.reconstruct',tile,tilebits[0]+2*tilebits[1]+4*tilebits[2])
    patchmask = s.geom(32,d*ef,'patch.mask')
    s.subset(15*patchmask,patch,'patch.digits')

    tile_row_radix = s.power(32,p,'tile.row_radix')
    tile_rows = s.spread(tile,tile_row_radix,qr,txrep,'tile.rows')
    tile_plane_radix = s.power(32,A*q,'tile.plane_radix')
    tile_planes = s.spread(tile_rows,tile_plane_radix,r,tyrep,'tile.planes')
    repeat_x = s.geom(tile_row_radix,txrep,'tile.repeat_x')
    repeat_y = s.geom(tile_plane_radix,tyrep,'tile.repeat_y')
    tile_z_radix = s.power(32,AB*r,'tile.z_radix')
    repeat_z = s.geom(tile_z_radix,tzrep,'tile.repeat_z')
    background = tile_planes*repeat_x*repeat_y*repeat_z
    patch_row_radix = s.power(32,d,'patch.row_radix')
    patch_rows = s.spread(patch,patch_row_radix,ef,pxrep,'patch.rows')
    patch_plane_radix = s.power(32,A*e,'patch.plane_radix')
    patch_planes = s.spread(patch_rows,patch_plane_radix,f,pyrep,'patch.planes')
    patch_shift = s.power(32,hx+A*hy+AB*hz,'patch.shift')
    additions = patch_planes*patch_shift

    X = s.power(32,A,'box.X')
    Y = s.power(X,B,'box.Y')
    Q = s.power(Y,C,'box.Q')
    jx,jy,jz = [s.natural('box.j'+axis) for axis in ['x','y','z']]
    s.equal('box.jx_equation',1024*(31*jx+1),X)
    s.equal('box.jy_equation',X*X*((X-1)*jy+1),Y)
    s.equal('box.jz_equation',Y*Y*((Y-1)*jz+1),Q)
    interior = 32*X*Y*jx*jy*jz

    K = s.positive('time.layers')
    endshift = s.power(Q,K,'time.endshift')
    repetition = s.natural('time.repetition')
    s.equal('time.repetition_equation',(Q-1)*repetition+1,endshift)
    pre,new,final = [s.natural('time.'+name) for name in ['pre','new','final']]
    interior_frames = interior*repetition
    s.subset(interior_frames,pre,'time.pre_mask')
    s.subset(interior_frames,new,'time.new_mask')
    s.subset(interior,final,'time.final_mask')
    s.equal('time.recurrence',Q*(pre+new),pre+endshift*final)
    nx,ny,nz = [s.natural('time.negative_'+axis) for axis in ['x','y','z']]
    s.equal('time.div_x',32*nx,pre)
    s.equal('time.div_y',X*ny,pre)
    s.equal('time.div_z',Y*nz,pre)
    available = (background+additions)*repetition+32*pre+X*pre+Y*pre+nx+ny+nz
    selected = s.intersection(available,31*new,'legality.select')
    slackbits = [s.natural('legality.bit'+str(i)) for i in range(5)]
    for i in range(5): s.subset(new,slackbits[i],'legality.allow'+str(i))
    s.subset(new,slackbits[3]+slackbits[4],'legality.exclude24_31')
    slack = slackbits[0]+2*slackbits[1]+4*slackbits[2]+8*slackbits[3]+16*slackbits[4]
    s.equal('legality.threshold',selected,6*new+slack)

    local = []
    for axis,z,halfextent,full in zip(['x','y','z'],zeta,[hx,hy,hz],[A,B,C]):
        h,sign,ell = [s.natural('target.'+axis+'.'+v) for v in ['halfcode','sign','local']]
        uppergap = s.positive('target.'+axis+'.uppergap')
        s.equal('target.'+axis+'.zigzag',z,2*h+sign)
        s.equal('target.'+axis+'.sign_binary',sign*(sign-1),0)
        s.equal('target.'+axis+'.translate',ell+2*sign*h+sign,halfextent+h)
        s.equal('target.'+axis+'.bound',ell+uppergap,full)
        local.append(ell)
    point = s.power(32,local[0]+A*local[1]+AB*local[2],'target.point')
    s.subset(final,point,'target.fired')

    ports = {'p':p,'q':q,'r':r,'d':d,'e':e,'f':f,'tile':tile,'patch':patch,
             'A':A,'B':B,'C':C,'X':X,'Y':Y,'Q':Q,'half_x':hx,'half_y':hy,'half_z':hz,
             'background':background,'additions':additions,'interior_mask':interior,
             'layers':K,'endshift':endshift,'repetition':repetition,
             'pre':pre,'new':new,'final':final,'available':available,'selected':selected,
             'legality_slack':slack,'target_point':point}
    for i,axis in enumerate(['x','y','z']):
        ports['zeta_'+axis]=zeta[i]
        ports['local_'+axis]=local[i]
    for label,expr in ports.items(): s.expose(label,expr)
    return s.combine()


def inspect(dag):
    degree = {'input:InputPlus':1}
    degree.update({'witness:'+name:1 for name in dag['witnesses']})
    def deg(ref):
        if ref.startswith('constant:'):
            int(ref[9:])
            return 0
        return degree[ref]
    for i,(op,a,b) in enumerate(dag['gates']):
        da,db=deg(a),deg(b)
        degree['gate:'+str(i)] = da+db if op=='*' else max(da,db)
    reachable=set()
    todo=[dag['output']]
    while todo:
        ref=todo.pop()
        if ref in reachable: continue
        reachable.add(ref)
        if ref.startswith('gate:'):
            todo.extend(dag['gates'][int(ref[5:])][1:])
    dead_gates=[i for i in range(len(dag['gates'])) if 'gate:'+str(i) not in reachable]
    dead_witnesses=[n for n in dag['witnesses'] if 'witness:'+n not in reachable]
    assert not dead_gates and not dead_witnesses
    counts=lambda items: dict(Counter(g[0] for g in items))
    return {'positive_witnesses':len(dag['witnesses']),
            'equalities':len(dag['equalities']),'gates':len(dag['gates']),
            'body_counts':counts(dag['gates'][:dag['body_gate_count']]),
            'sos_counts':counts(dag['gates'][dag['body_gate_count']:]),
            'full_counts':counts(dag['gates']),
            'macros':dict(Counter(m['kind'] for m in dag['macros'])),
            'degree_upper_bound':degree[dag['output']],
            'dead_gates':dead_gates,'dead_witnesses':dead_witnesses,
            'ports':len(dag['ports'])}


if __name__=='__main__':
    dag=construct()
    receipt=inspect(dag)
    raw=(json.dumps(dag,sort_keys=True,separators=(',',':'))+'\n').encode()
    receipt['dag_sha256']=hashlib.sha256(raw).hexdigest()
    receipt['builder_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    target=ROOT/'evidence'
    target.mkdir(exist_ok=True)
    (target/'polynomial-dag.json').write_bytes(raw)
    (target/'build-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))
