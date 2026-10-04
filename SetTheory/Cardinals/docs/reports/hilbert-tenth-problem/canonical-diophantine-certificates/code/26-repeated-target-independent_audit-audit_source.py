#!/usr/bin/env python3
"""Fresh adversarial auditor. Only standard library; submitted files are inert data.

This reconstructs the certificate specification in a separate sparse-polynomial
implementation, compares every clause/interface/port, and checks the literal SOS.
No submitted executable, prior checker, or Lean code is imported or run.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

ROOT=Path('/workspace/shared/sandpile-repeated-target-20261004')
OUT=Path(__file__).resolve().parent
DAG_PIN='7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6'

class F:
    def __init__(self, data):
        if isinstance(data,F): self.d=data.d
        elif isinstance(data,int): self.d={():data} if data else {}
        elif isinstance(data,str): self.d={(data,):1}
        else: self.d={m:c for m,c in data.items() if c}
    def __add__(self,o):
        q=self.d.copy()
        for m,c in F(o).d.items():q[m]=q.get(m,0)+c
        return F(q)
    __radd__=__add__
    def __neg__(self):return F({m:-c for m,c in self.d.items()})
    def __sub__(self,o):return self+-F(o)
    def __rsub__(self,o):return F(o)+-self
    def __mul__(self,o):
        q={}
        for a,c in self.d.items():
            for b,d in F(o).d.items():
                m=tuple(sorted(a+b));q[m]=q.get(m,0)+c*d
        return F(q)
    __rmul__=__mul__
    def __pow__(self,n):
        assert n>=0
        p=F(1)
        for _ in range(n):p=p*self
        return p
    def __eq__(self,o):return self.d==F(o).d
    def degree(self):return max(map(len,self.d),default=-1)
    def top(self):return F({m:c for m,c in self.d.items() if len(m)==self.degree()})

class Specification:
    def __init__(self):
        self.vars=set();self.clauses={};self.macros={}
    def v(self,name):
        assert name not in self.vars, name
        self.vars.add(name);return F('witness:'+name)
    def natural(self,name):return self.v(name+'.Plus')-1
    def eq(self,name,left,right):
        assert name not in self.clauses,name
        self.clauses[name]=F(left)-F(right)
    def interface(self,name,kind,**values):
        assert name not in self.macros,name
        self.macros[name]={'kind':kind,**{k:F(v) for k,v in values.items()}}
    def exp(self,base,e,name):
        # Direct stated Pell specialization, independently represented.
        b=F(base);k=F(e)+1
        out=self.v(name+'.out');a=self.v(name+'.aMinus1')+1
        beta=self.v(name+'.betaMinus1')+1
        w,M,g,x,y,u,v,s,t,qb,qv,strict=[self.v(name+'.'+z) for z in
            ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')]
        dz={z:self.natural(name+'.'+z) for z in
            ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2')}
        # Residual expressions deliberately independent of source gate order.
        residuals=[
            x**2-1-(a**2-1)*y**2,
            u**2-1-(a**2-1)*v**2,
            s**2-1-(beta**2-1)*t**2,
            beta-1-4*y*qb,
            beta-a+u*(dz['alpha1']-dz['alpha2']),
            v-y**2*qv,
            s-x+u*(dz['sigma1']-dz['sigma2']),
            t-k+4*y*(dz['tau1']-dz['tau2']),
            y-k-dz['dyk'],w-b-dz['dwb'],w-k-dz['dwk'],
            M-b*out-strict,
            a**2-1-((w+1)**2-1)*w**2*g**2,
            2*a*b-M-b**2-1,
            x-y*(a-b)-b*out+M*(dz['rho1']-dz['rho2'])]
        for i,r in enumerate(residuals,1):self.eq(name+'.eq'+str(i),r,0)
        self.interface(name,'power',base=b,exponent=e,out=out)
        return out
    def subset(self,mask,value,name):
        R=self.exp(2,F(mask)+1,name+'.radix')
        slot=self.exp(R,value,name+'.slot')
        z=self.exp(R+1,mask,name+'.binomial')
        q=self.natural(name+'.quotient');h=self.natural(name+'.half');r=self.natural(name+'.remainder')
        gd=self.v(name+'.digit_gap');gr=self.v(name+'.remainder_gap')
        self.eq(name+'.extract',z,(q*R+2*h+1)*slot+r)
        self.eq(name+'.digit_bound',2*h+1+gd,R)
        self.eq(name+'.remainder_bound',r+gr,slot)
        self.interface(name,'subset',mask=mask,value=value)
    def intersection(self,left,right,name):
        common=self.natural(name+'.common');a=self.natural(name+'.left_only');c=self.natural(name+'.right_only')
        self.eq(name+'.left_partition',left,common+a)
        self.eq(name+'.right_partition',right,common+c)
        self.subset(left,common,name+'.left');self.subset(right,common,name+'.right')
        self.subset(a+c,a,name+'.disjoint')
        self.interface(name,'and',left=left,right=right,out=common)
        return common
    def spread(self,u,base,n,stride,name):
        b=F(base);s=F(stride)
        gap=self.natural(name+'.stride_gap');strict=self.v(name+'.range_gap')
        self.eq(name+'.stride_bound',s,F(n)+1+gap)
        limit=self.exp(b,n,name+'.range');self.eq(name+'.range_bound',F(u)+strict,limit)
        copybase=self.exp(b,s-1,name+'.copybase');copylimit=self.exp(copybase,n,name+'.copylimit')
        copy=self.natural(name+'.copy');mask=self.natural(name+'.mask')
        self.eq(name+'.copy_equation',(copybase-1)*copy+1,copylimit)
        self.eq(name+'.mask_equation',(b*copybase-1)*mask+1,copylimit*limit)
        out=self.intersection(F(u)*copy,(b-1)*mask,name+'.select')
        self.interface(name,'spread',value=u,base=b,length=n,stride=s,out=out)
        return out
    def geom(self,b,n,name):
        value=self.natural(name+'.value');power=self.exp(b,n,name+'.power')
        self.eq(name+'.equation',(F(b)-1)*value+1,power);return value


def specification():
    S=Specification()
    dims={n:S.v('descriptor.'+n) for n in 'pqrdef'}
    p,q,r,d,e,f=[dims[n] for n in 'pqrdef']
    T=S.natural('descriptor.tile');D=S.natural('descriptor.patch')
    z={a:S.natural('target.zeta'+a) for a in 'xyz'}
    fields=[p-1,q-1,r-1,T,d-1,e-1,f-1,D,z['x'],z['y'],z['z']]
    codes=[F('input:InputPlus')-1]+[S.natural('descriptor.pair'+str(i)) for i in range(1,10)]
    for i in range(10):
        tail=codes[i+1] if i<9 else fields[10]
        total=fields[i]+tail
        S.eq('descriptor.cantor'+str(i),2*codes[i],total**2+total+2*tail)
    tm=S.geom(32,p*q*r,'tile.mask')
    bits=[S.natural('tile.bit'+str(i)) for i in range(3)]
    for i,v in enumerate(bits):S.subset(tm,v,'tile.allow'+str(i))
    S.subset(tm,bits[1]+bits[2],'tile.exclude67')
    S.eq('tile.reconstruct',T,bits[0]+2*bits[1]+4*bits[2])
    dm=S.geom(32,d*e*f,'patch.mask');S.subset(15*dm,D,'patch.digits')
    K=S.v('time.layers');L=S.v('radix.width')
    b=S.exp(32,L,'radix.base');h=S.v('radix.half');gg=S.natural('radix.growth_gap')
    S.eq('radix.half_equation',2*h,b);S.eq('radix.growth_equation',b,64*K+64+gg)
    Tb=S.spread(T,32,p*q*r,L,'tile.convert');Db=S.spread(D,32,d*e*f,L,'patch.convert')
    tx,ty,tz=[S.v('box.t'+a)+1 for a in 'xyz']
    hx=p*d*tx;hy=q*e*ty;hz=r*f*tz
    A=2*hx;B=2*hy;C=2*hz
    tr=S.exp(b,p,'tile.row_radix')
    tiled_rows=S.spread(Tb,tr,q*r,2*d*tx,'tile.rows')
    tp=S.exp(b,A*q,'tile.plane_radix')
    tiled_planes=S.spread(tiled_rows,tp,r,2*e*ty,'tile.planes')
    xr=S.geom(tr,2*d*tx,'tile.repeat_x');yr=S.geom(tp,2*e*ty,'tile.repeat_y')
    tzr=S.exp(b,A*B*r,'tile.z_radix');zr=S.geom(tzr,2*f*tz,'tile.repeat_z')
    background=tiled_planes*xr*yr*zr
    pr=S.exp(b,d,'patch.row_radix');patch_rows=S.spread(Db,pr,e*f,2*p*tx,'patch.rows')
    pp=S.exp(b,A*e,'patch.plane_radix');patch_planes=S.spread(patch_rows,pp,f,2*q*ty,'patch.planes')
    shifted=S.exp(b,hx+A*hy+A*B*hz,'patch.shift');additions=patch_planes*shifted
    X=S.exp(b,A,'box.X');Y=S.exp(X,B,'box.Y');Q=S.exp(Y,C,'box.Q')
    jx,jy,jz=[S.natural('box.j'+a) for a in 'xyz']
    S.eq('box.jx_equation',b**2*((b-1)*jx+1),X)
    S.eq('box.jy_equation',X**2*((X-1)*jy+1),Y)
    S.eq('box.jz_equation',Y**2*((Y-1)*jz+1),Q)
    I=b*X*Y*jx*jy*jz
    W=S.exp(Q,K,'time.endshift');R=S.natural('time.repetition')
    S.eq('time.repetition_equation',(Q-1)*R+1,W)
    pre=S.natural('time.pre');event=S.natural('time.event');final=S.natural('time.final')
    S.subset((b-1)*I*R,pre,'time.pre_mask');S.subset(I*R,event,'time.event_mask')
    S.subset((b-1)*I,final,'time.final_mask')
    S.eq('time.recurrence',Q*(pre+event),pre+W*final)
    nx,ny,nz=[S.natural('time.negative_'+a) for a in 'xyz']
    for name,radix,v in [('x',b,nx),('y',X,ny),('z',Y,nz)]:S.eq('time.div_'+name,radix*v,pre)
    available=(background+additions)*R+(b+X+Y)*pre+nx+ny+nz
    selected=S.intersection(available,(b-1)*event,'legality.available')
    self_selected=S.intersection(pre,(b-1)*event,'legality.self')
    slack=S.natural('legality.slack');S.subset((h-1)*event,slack,'legality.slack_mask')
    S.eq('legality.threshold',selected,6*(self_selected+event)+slack)
    local={}
    for axis,extent in zip('xyz',[hx,hy,hz]):
        hc=S.natural('target.'+axis+'.halfcode');sg=S.natural('target.'+axis+'.sign')
        ell=S.natural('target.'+axis+'.local');upper=S.v('target.'+axis+'.uppergap')
        S.eq('target.'+axis+'.zigzag',z[axis],2*hc+sg)
        S.eq('target.'+axis+'.sign_binary',sg**2-sg,0)
        S.eq('target.'+axis+'.translate',ell+2*sg*hc+sg,extent+hc)
        S.eq('target.'+axis+'.bound',ell+upper,2*extent)
        local[axis]=ell
    point=S.exp(b,local['x']+A*local['y']+A*B*local['z'],'target.point')
    tau=S.natural('target.time');timepoint=S.exp(Q,tau,'target.timepoint')
    S.subset(event,point*timepoint,'target.fired')
    S.ports={**dims,'tile':T,'patch':D,'radix':b,'radix_width':L,'radix_half':h,
        'tile_converted':Tb,'patch_converted':Db,'A':A,'B':B,'C':C,'X':X,'Y':Y,'Q':Q,
        'half_x':hx,'half_y':hy,'half_z':hz,'background':background,'additions':additions,
        'interior_mask':I,'layers':K,'endshift':W,'repetition':R,'pre':pre,'event':event,'final':final,
        'available':available,'selected':selected,'self_selected':self_selected,'legality_slack':slack,
        'target_point':point,'target_time':tau,'target_timepoint':timepoint,
        **{'zeta_'+a:z[a] for a in 'xyz'},**{'local_'+a:local[a] for a in 'xyz'}}
    return S


def audit():
    raw=(ROOT/'evidence/polynomial-dag.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==DAG_PIN
    d=json.loads(raw)
    assert d['schema']=='fixed-positive-integer-polynomial-dag-v1'
    assert d['input']=='InputPlus'
    assert d['domain']=='InputPlus and every witness are positive integers'
    assert len(set(d['witnesses']))==len(d['witnesses'])
    spec=specification()
    assert set(d['witnesses'])==spec.vars,(set(d['witnesses'])^spec.vars)
    body=d['body_gate_count'];gates=d['gates']
    values={'input:InputPlus':F('input:InputPlus'),**{'witness:'+v:F('witness:'+v) for v in d['witnesses']}}
    def resolve(ref):
        if ref.startswith('constant:'):return F(int(ref[9:]))
        assert ref in values,ref
        return values[ref]
    for i,g in enumerate(gates):
        assert isinstance(g,list) and len(g)==3
        op,ar,br=g;assert op in ('+','-','*')
        for ref in (ar,br):
            if ref.startswith('gate:'):assert 0<=int(ref[5:])<i
            elif ref.startswith('constant:'):assert str(int(ref[9:]))==ref[9:]
            else:assert ref in values,ref
        if i<body:
            a=resolve(ar);b=resolve(br)
            values['gate:'+str(i)]=a+b if op=='+' else (a-b if op=='-' else a*b)
    assert len(set(x[2] for x in d['equalities']))==len(d['equalities'])
    assert set(x[2] for x in d['equalities'])==set(spec.clauses)
    residuals={}
    for ar,br,name in d['equalities']:
        poly=resolve(ar)-resolve(br)
        assert poly==spec.clauses[name],name
        residuals[name]=poly
    assert len(d['macros'])==len(spec.macros)
    assert len({m['name'] for m in d['macros']})==len(d['macros'])
    for macro in d['macros']:
        expect=spec.macros[macro['name']]
        assert set(macro)==set(expect)|{'name'}
        for k,v in expect.items():
            if k=='kind':assert macro[k]==v
            else:assert resolve(macro[k])==v,(macro['name'],k)
    assert set(d['ports'])==set(spec.ports)
    for k,v in spec.ports.items():assert resolve(d['ports'][k])==v,('port',k)
    # The actual output is an exact ordered sum of each listed residual squared.
    idx=body;squares=[]
    for a,b,name in d['equalities']:
        assert gates[idx]==['-',a,b];ref='gate:'+str(idx);idx+=1
        assert gates[idx]==['*',ref,ref];squares.append('gate:'+str(idx));idx+=1
    output=squares[0]
    for square in squares[1:]:
        assert gates[idx]==['+',output,square];output='gate:'+str(idx);idx+=1
    assert idx==len(gates) and output==d['output']
    live=set();todo=[output]
    while todo:
        r=todo.pop()
        if r in live:continue
        live.add(r)
        if r.startswith('gate:'):todo.extend(gates[int(r[5:])][1:])
    assert all('gate:'+str(i) in live for i in range(len(gates)))
    assert all('witness:'+w in live for w in d['witnesses'])
    assert 'input:InputPlus' in live
    degree=max(r.degree() for r in residuals.values())
    highest={name:r.top() for name,r in residuals.items() if r.degree()==degree}
    top_sos=sum((r*r for r in highest.values()),F(0))
    assert degree==9
    assert set(highest)=={'patch.shift.eq8','patch.shift.eq9','patch.shift.eq11'}
    expected_vars=tuple(sorted('witness:'+s for s in ['descriptor.'+z for z in 'pqrdef']+['box.t'+a for a in 'xyz']))
    assert all(p==F({expected_vars:-4}) for p in highest.values())
    assert top_sos==F({tuple(sorted(expected_vars*2)):48})
    assert (len(d['witnesses']),len(d['equalities']),len(gates))==(3865,2251,17275)
    counts=dict(Counter(m['kind'] for m in d['macros']))
    assert counts=={'power':138,'subset':34,'and':8,'spread':6}
    def ops(gs):return dict(Counter(g[0] for g in gs))
    result={
        'verdict':'PASS','source_sha256':DAG_PIN,
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'positive_witnesses':len(d['witnesses']),'exact_clause_matches':len(residuals),
        'exact_interface_matches':len(d['macros']),'exact_port_matches':len(d['ports']),
        'gates':len(gates),'body_gates':body,'body_operations':ops(gates[:body]),
        'sos_operations':ops(gates[body:]),'all_operations':ops(gates),'macros':counts,
        'max_body_monomials':max(len(p.d) for p in values.values()),
        'residual_degree_histogram':dict(sorted(Counter(r.degree() for r in residuals.values()).items())),
        'exact_degree':degree*2,'leading_coefficient':48,'leading_squared_monomial_variables':list(expected_vars),
        'ordered_SOS_exact':True,'all_gates_witnesses_input_live':True,
        'submitted_programs_executed_or_imported':False}
    (OUT/'source-audit-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':audit()
