#!/usr/bin/env python3
"""Literal fixed-arity polynomial for unrestricted finite target firing.

Freshly authored source. No earlier builder/checker is run or imported.
Every source-construction loop has a fixed, input-independent length.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


class Term:
    def __init__(self, source, ref):
        self.source, self.ref = source, ref
    def __add__(self, other): return self.source.binary('+', self, other)
    def __radd__(self, other): return self.source.binary('+', other, self)
    def __sub__(self, other): return self.source.binary('-', self, other)
    def __rsub__(self, other): return self.source.binary('-', other, self)
    def __mul__(self, other): return self.source.binary('*', self, other)
    def __rmul__(self, other): return self.source.binary('*', other, self)


class Polynomial:
    def __init__(self):
        self.witnesses, self.gates, self.equalities, self.macros = [], [], [], []
        self.ports = {}
        self.input = Term(self, 'input:InputPlus')
    def term(self, value):
        if isinstance(value, Term):
            assert value.source is self
            return value
        assert isinstance(value, int)
        return Term(self, 'constant:' + str(value))
    def binary(self, op, left, right):
        assert op in ('+', '-', '*')
        self.gates.append([op, self.term(left).ref, self.term(right).ref])
        return Term(self, 'gate:' + str(len(self.gates) - 1))
    def pos(self, name):
        assert name not in self.witnesses
        self.witnesses.append(name)
        return Term(self, 'witness:' + name)
    def nat(self, name): return self.pos(name + '.Plus') - 1
    def eq(self, name, left, right):
        assert name not in [v[2] for v in self.equalities]
        self.equalities.append([self.term(left).ref, self.term(right).ref, name])
    def macro(self, kind, name, **ports):
        self.macros.append(dict(kind=kind, name=name,
                                **{k:self.term(v).ref for k,v in ports.items()}))
    def power(self, base, exponent, name):
        b, n = self.term(base), self.term(exponent)
        out = self.pos(name + '.out')
        a = self.pos(name + '.aMinus1') + 1
        beta = self.pos(name + '.betaMinus1') + 1
        pp = {k:self.pos(name + '.' + k) for k in
              ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')}
        nn = {k:self.nat(name + '.' + k) for k in
              ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2',
               'tau1','tau2','rho1','rho2')}
        w,M,g,x,y,u,v,s,t,qb,qv,strict = [pp[k] for k in
              ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')]
        k, m = n+1, b*out
        aa, yy, bb, foury = a*a, y*y, beta*beta, 4*y
        delta, wp, wg = aa-1, w+1, w*g
        pairs = [
            (x*x, 1+delta*yy), (u*u, 1+delta*(v*v)),
            (s*s, 1+(bb-1)*(t*t)), (beta, 1+foury*qb),
            (beta+u*nn['alpha1'], a+u*nn['alpha2']), (v, yy*qv),
            (s+u*nn['sigma1'], x+u*nn['sigma2']),
            (t+foury*nn['tau1'], k+foury*nn['tau2']),
            (y, k+nn['dyk']), (w, b+nn['dwb']), (w, k+nn['dwk']),
            (M, m+strict), (aa, 1+(wp*wp-1)*(wg*wg)),
            (2*a*b, M+(b*b+1)),
            (x+M*nn['rho1'], y*(a-b)+m+M*nn['rho2'])]
        for j,(left,right) in enumerate(pairs,1): self.eq(name+'.eq'+str(j),left,right)
        self.macro('power',name,base=b,exponent=n,out=out)
        return out
    def geometric(self, base, length, name):
        b,n = self.term(base),self.term(length)
        value=self.nat(name+'.value')
        end=self.power(b,n,name+'.power')
        self.eq(name+'.equation',(b-1)*value+1,end)
        return value
    def subset(self, mask, value, name):
        M,V=self.term(mask),self.term(value)
        radix=self.power(2,M+1,name+'.radix')
        slot=self.power(radix,V,name+'.slot')
        expansion=self.power(radix+1,M,name+'.binomial')
        q,h,r=[self.nat(name+'.'+k) for k in ('quotient','half','remainder')]
        dg,rg=[self.pos(name+'.'+k) for k in ('digit_gap','remainder_gap')]
        odd=2*h+1
        self.eq(name+'.extract',expansion,(q*radix+odd)*slot+r)
        self.eq(name+'.digit_bound',odd+dg,radix)
        self.eq(name+'.remainder_bound',r+rg,slot)
        self.macro('subset',name,mask=M,value=V)
    def intersect(self, left, right, name):
        x,y=self.term(left),self.term(right)
        z,a,c=[self.nat(name+'.'+k) for k in ('common','left_only','right_only')]
        self.eq(name+'.left_partition',x,z+a)
        self.eq(name+'.right_partition',y,z+c)
        self.subset(x,z,name+'.left')
        self.subset(y,z,name+'.right')
        self.subset(a+c,a,name+'.disjoint')
        self.macro('and',name,left=x,right=y,out=z)
        return z
    def spread(self, value, base, length, stride, name):
        u,b,n,s=map(self.term,(value,base,length,stride))
        gap=self.nat(name+'.stride_gap')
        strict=self.pos(name+'.range_gap')
        self.eq(name+'.stride_bound',s,n+1+gap)
        limit=self.power(b,n,name+'.range')
        self.eq(name+'.range_bound',u+strict,limit)
        cb=self.power(b,s-1,name+'.copybase')
        end=self.power(cb,n,name+'.copylimit')
        copy,mask=self.nat(name+'.copy'),self.nat(name+'.mask')
        self.eq(name+'.copy_equation',(cb-1)*copy+1,end)
        self.eq(name+'.mask_equation',(b*cb-1)*mask+1,end*limit)
        out=self.intersect(u*copy,(b-1)*mask,name+'.select')
        self.macro('spread',name,value=u,base=b,length=n,stride=s,out=out)
        return out
    def finish(self):
        body=len(self.gates)
        squares=[]
        for left,right,_ in self.equalities:
            residual=Term(self,left)-Term(self,right)
            squares.append(residual*residual)
        output=squares[0]
        for square in squares[1:]:output=output+square
        return dict(schema='fixed-positive-integer-polynomial-dag-v1',input='InputPlus',
                    domain='InputPlus and every witness are positive integers',
                    constants='Fixed integer literals are free; every binary arithmetic gate is counted',
                    witnesses=self.witnesses,gates=self.gates,equalities=self.equalities,
                    macros=self.macros,ports=self.ports,output=output.ref,body_gate_count=body)


def construct():
    S=Polynomial()
    p,q,r,d,e,f=[S.pos('descriptor.'+a) for a in ('p','q','r','d','e','f')]
    tile,patch=S.nat('descriptor.tile'),S.nat('descriptor.patch')
    zeta=[S.nat('target.zeta'+a) for a in ('x','y','z')]
    fields=[p-1,q-1,r-1,tile,d-1,e-1,f-1,patch]+zeta
    rest=fields[-1]
    for j in range(9,-1,-1):
        code=S.input-1 if j==0 else S.nat('descriptor.pair'+str(j))
        joined=fields[j]+rest
        S.eq('descriptor.cantor'+str(j),2*code,joined*(joined+1)+2*rest)
        rest=code

    # Ordinary input data remain base 32. Their interpretation is unchanged.
    tile_volume,patch_volume=p*q*r,d*e*f
    tile_mask=S.geometric(32,tile_volume,'tile.mask')
    bit=[S.nat('tile.bit'+str(j)) for j in range(3)]
    for j in range(3):S.subset(tile_mask,bit[j],'tile.allow'+str(j))
    S.subset(tile_mask,bit[1]+bit[2],'tile.exclude67')
    S.eq('tile.reconstruct',tile,bit[0]+2*bit[1]+4*bit[2])
    patch_mask=S.geometric(32,patch_volume,'patch.mask')
    S.subset(15*patch_mask,patch,'patch.digits')

    K=S.pos('time.layers')
    width=S.pos('radix.width')
    b=S.power(32,width,'radix.base')
    half=S.pos('radix.half')
    growth=S.nat('radix.growth_gap')
    S.eq('radix.half_equation',2*half,b)
    S.eq('radix.growth_equation',b,64*(K+1)+growth)
    tile_b=S.spread(tile,32,tile_volume,width,'tile.convert')
    patch_b=S.spread(patch,32,patch_volume,width,'patch.convert')

    tx,ty,tz=[S.pos('box.t'+a)+1 for a in ('x','y','z')]
    hx,hy,hz=p*d*tx,q*e*ty,r*f*tz
    A,B,C=2*hx,2*hy,2*hz
    AB=A*B
    txr,tyr,tzr=2*d*tx,2*e*ty,2*f*tz
    pxr,pyr=2*p*tx,2*q*ty
    row=S.power(b,p,'tile.row_radix')
    rows=S.spread(tile_b,row,q*r,txr,'tile.rows')
    plane=S.power(b,A*q,'tile.plane_radix')
    planes=S.spread(rows,plane,r,tyr,'tile.planes')
    rx=S.geometric(row,txr,'tile.repeat_x')
    ry=S.geometric(plane,tyr,'tile.repeat_y')
    zradix=S.power(b,AB*r,'tile.z_radix')
    rz=S.geometric(zradix,tzr,'tile.repeat_z')
    background=planes*rx*ry*rz
    prow=S.power(b,d,'patch.row_radix')
    prows=S.spread(patch_b,prow,e*f,pxr,'patch.rows')
    pplane=S.power(b,A*e,'patch.plane_radix')
    pplanes=S.spread(prows,pplane,f,pyr,'patch.planes')
    shift=S.power(b,hx+A*hy+AB*hz,'patch.shift')
    additions=pplanes*shift

    X=S.power(b,A,'box.X')
    Y=S.power(X,B,'box.Y')
    Q=S.power(Y,C,'box.Q')
    jx,jy,jz=[S.nat('box.j'+a) for a in ('x','y','z')]
    S.eq('box.jx_equation',b*b*((b-1)*jx+1),X)
    S.eq('box.jy_equation',X*X*((X-1)*jy+1),Y)
    S.eq('box.jz_equation',Y*Y*((Y-1)*jz+1),Q)
    interior=b*X*Y*jx*jy*jz
    end=S.power(Q,K,'time.endshift')
    repetition=S.nat('time.repetition')
    S.eq('time.repetition_equation',(Q-1)*repetition+1,end)
    pre,event,final=[S.nat('time.'+k) for k in ('pre','event','final')]
    interior_frames=interior*repetition
    S.subset((b-1)*interior_frames,pre,'time.pre_mask')
    S.subset(interior_frames,event,'time.event_mask')
    S.subset((b-1)*interior,final,'time.final_mask')
    S.eq('time.recurrence',Q*(pre+event),pre+end*final)
    nx,ny,nz=[S.nat('time.negative_'+a) for a in ('x','y','z')]
    S.eq('time.div_x',b*nx,pre)
    S.eq('time.div_y',X*ny,pre)
    S.eq('time.div_z',Y*nz,pre)
    available=(background+additions)*repetition+b*pre+X*pre+Y*pre+nx+ny+nz
    select_mask=(b-1)*event
    selected=S.intersect(available,select_mask,'legality.available')
    self_selected=S.intersect(pre,select_mask,'legality.self')
    slack=S.nat('legality.slack')
    S.subset((half-1)*event,slack,'legality.slack_mask')
    S.eq('legality.threshold',selected,6*self_selected+6*event+slack)

    local=[]
    for axis,z,halfextent,full in zip(('x','y','z'),zeta,(hx,hy,hz),(A,B,C)):
        h,sign,ell=[S.nat('target.'+axis+'.'+n) for n in ('halfcode','sign','local')]
        gap=S.pos('target.'+axis+'.uppergap')
        S.eq('target.'+axis+'.zigzag',z,2*h+sign)
        S.eq('target.'+axis+'.sign_binary',sign*(sign-1),0)
        S.eq('target.'+axis+'.translate',ell+2*sign*h+sign,halfextent+h)
        S.eq('target.'+axis+'.bound',ell+gap,full)
        local.append(ell)
    point=S.power(b,local[0]+A*local[1]+AB*local[2],'target.point')
    tau=S.nat('target.time')
    timepoint=S.power(Q,tau,'target.timepoint')
    S.subset(event,point*timepoint,'target.fired')

    ports=dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=tile,patch=patch,
               radix=b,radix_width=width,radix_half=half,tile_converted=tile_b,
               patch_converted=patch_b,A=A,B=B,C=C,X=X,Y=Y,Q=Q,
               half_x=hx,half_y=hy,half_z=hz,background=background,
               additions=additions,interior_mask=interior,layers=K,
               endshift=end,repetition=repetition,pre=pre,event=event,final=final,
               available=available,selected=selected,self_selected=self_selected,
               legality_slack=slack,target_point=point,target_time=tau,target_timepoint=timepoint)
    for j,axis in enumerate(('x','y','z')):
        ports['zeta_'+axis]=zeta[j]
        ports['local_'+axis]=local[j]
    S.ports={name:S.term(value).ref for name,value in ports.items()}
    return S.finish()


def inspect(dag):
    degrees={'input:InputPlus':1,**{'witness:'+w:1 for w in dag['witnesses']}}
    def degree(ref):return 0 if ref.startswith('constant:') else degrees[ref]
    for j,(op,a,b) in enumerate(dag['gates']):
        da,db=degree(a),degree(b)
        degrees['gate:'+str(j)]=da+db if op=='*' else max(da,db)
    seen=set();pending=[dag['output']]
    while pending:
        ref=pending.pop()
        if ref in seen:continue
        seen.add(ref)
        if ref.startswith('gate:'):pending.extend(dag['gates'][int(ref[5:])][1:])
    dead_gates=[j for j in range(len(dag['gates'])) if 'gate:'+str(j) not in seen]
    dead_witnesses=[w for w in dag['witnesses'] if 'witness:'+w not in seen]
    assert not dead_gates and not dead_witnesses
    count=lambda gs:dict(Counter(g[0] for g in gs))
    body=dag['body_gate_count']
    return dict(positive_witnesses=len(dag['witnesses']),equalities=len(dag['equalities']),
                gates=len(dag['gates']),body_counts=count(dag['gates'][:body]),
                sos_counts=count(dag['gates'][body:]),full_counts=count(dag['gates']),
                macros=dict(Counter(m['kind'] for m in dag['macros'])),
                degree_upper_bound=degree(dag['output']),ports=len(dag['ports']),
                dead_gates=dead_gates,dead_witnesses=dead_witnesses)


if __name__=='__main__':
    source=construct();receipt=inspect(source)
    raw=(json.dumps(source,sort_keys=True,separators=(',',':'))+'\n').encode()
    receipt['dag_sha256']=hashlib.sha256(raw).hexdigest()
    receipt['builder_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/'evidence').mkdir(exist_ok=True)
    (HERE/'evidence/polynomial-dag.json').write_bytes(raw)
    (HERE/'evidence/build-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))
