#!/usr/bin/env python3
"""Independent exact formal-polynomial audit of an inert JSON certificate.

This program neither imports nor executes any submitted or historical program.
It specifies intended residuals and interfaces using a separate sparse polynomial
algebra, reads the DAG strictly as data, and compares exact polynomials over Z.
The sequential sum-of-squares assembly is checked structurally to avoid retaining
thousands of redundant expanding prefix sums. No witness evaluation is used.
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path('/workspace/shared/sandpile-repeated-target-20261004')
DAG_FILE = ROOT / 'evidence/polynomial-dag.json'
FROZEN_SHA256 = '7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6'
HERE = Path(__file__).resolve().parent

class Poly:
    """Sparse Z polynomial; monomials are sorted tuples of variable IDs."""
    ids = {}
    def __init__(self, terms=None):
        self.terms = {m:c for m,c in (terms or {}).items() if c}
    @classmethod
    def integer(cls, x):
        assert type(x) is int
        return cls({():x})
    @classmethod
    def var(cls, name):
        if name not in cls.ids:
            cls.ids[name] = len(cls.ids)
        return cls({(cls.ids[name],):1})
    @staticmethod
    def coerce(x):
        return x if isinstance(x,Poly) else Poly.integer(x)
    def __add__(self, other):
        out = self.terms.copy()
        for m,c in self.coerce(other).terms.items():
            out[m] = out.get(m,0)+c
            if not out[m]: del out[m]
        return Poly(out)
    __radd__ = __add__
    def __neg__(self):
        return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self, other): return self + (-self.coerce(other))
    def __rsub__(self, other): return self.coerce(other) + (-self)
    def __mul__(self, other):
        out={}
        for m,c in self.terms.items():
            for n,d in self.coerce(other).terms.items():
                k=tuple(sorted(m+n))
                out[k]=out.get(k,0)+c*d
        return Poly(out)
    __rmul__=__mul__
    def __eq__(self, other): return self.terms == self.coerce(other).terms
    def degree(self): return max(map(len,self.terms),default=-1)
    def top(self):
        d=self.degree()
        return Poly({m:c for m,c in self.terms.items() if len(m)==d})
    def text(self):
        names={v:k for k,v in self.ids.items()}
        return [{'coefficient':c,'variables':[names[i] for i in m]}
                for m,c in sorted(self.terms.items())]

class Intended:
    """Contract-level specifications; no gate construction or source references."""
    def __init__(self):
        self.witnesses=set()
        self.residuals={}
        self.macros={}
        self.input=Poly.var('input:InputPlus')
    def positive(self,name):
        assert name not in self.witnesses, name
        self.witnesses.add(name)
        return Poly.var('witness:'+name)
    def natural(self,name): return self.positive(name+'.Plus')-1
    def equation(self,name,residual):
        assert name not in self.residuals,name
        self.residuals[name]=Poly.coerce(residual)
    def interface(self,kind,name,**ports):
        assert name not in self.macros,name
        self.macros[name]=(kind,{k:Poly.coerce(v) for k,v in ports.items()})
    def power(self,b,e,name):
        # The fifteen equations of the inherited constructive Pell power test.
        o=self.positive(name+'.out')
        a=self.positive(name+'.aMinus1')+1
        beta=self.positive(name+'.betaMinus1')+1
        pos={x:self.positive(name+'.'+x) for x in
             ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')}
        nat={x:self.natural(name+'.'+x) for x in
             ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2',
              'tau1','tau2','rho1','rho2')}
        w,M,g,x,y,u,v,s,t,qb,qv,strict=[pos[z] for z in
             ('w','modulus','g','x','y','u','v','s','t','qb','qv','strict')]
        k=e+1
        residuals={
          1:x*x-1-(a*a-1)*y*y,
          2:u*u-1-(a*a-1)*v*v,
          3:s*s-1-(beta*beta-1)*t*t,
          4:beta-1-4*y*qb,
          5:beta-a+u*(nat['alpha1']-nat['alpha2']),
          6:v-y*y*qv,
          7:s-x+u*(nat['sigma1']-nat['sigma2']),
          8:t-k+4*y*(nat['tau1']-nat['tau2']),
          9:y-k-nat['dyk'],
          10:w-b-nat['dwb'],
          11:w-k-nat['dwk'],
          12:M-b*o-strict,
          13:a*a-1-((w+1)*(w+1)-1)*w*w*g*g,
          14:2*a*b-M-b*b-1,
          15:x-y*(a-b)-b*o+M*(nat['rho1']-nat['rho2']),
        }
        for i,residual in residuals.items():self.equation(name+'.eq'+str(i),residual)
        self.interface('power',name,base=b,exponent=e,out=o)
        return o
    def subset(self,M,V,name):
        # Odd binomial digit, two strict bounds, and three exact powers.
        B=self.power(2,M+1,name+'.radix')
        position=self.power(B,V,name+'.slot')
        binomial=self.power(B+1,M,name+'.binomial')
        q,h,r=(self.natural(name+'.'+s) for s in ('quotient','half','remainder'))
        d=self.positive(name+'.digit_gap')
        g=self.positive(name+'.remainder_gap')
        self.equation(name+'.extract',binomial-q*B*position-(2*h+1)*position-r)
        self.equation(name+'.digit_bound',2*h+1+d-B)
        self.equation(name+'.remainder_bound',r+g-position)
        self.interface('subset',name,mask=M,value=V)
    def meet(self,x,y,name):
        z=self.natural(name+'.common')
        a=self.natural(name+'.left_only')
        c=self.natural(name+'.right_only')
        self.equation(name+'.left_partition',x-z-a)
        self.equation(name+'.right_partition',y-z-c)
        self.subset(x,z,name+'.left')
        self.subset(y,z,name+'.right')
        self.subset(a+c,a,name+'.disjoint')
        self.interface('and',name,left=x,right=y,out=z)
        return z
    def spread(self,u,b,n,stride,name):
        gap=self.natural(name+'.stride_gap')
        strict=self.positive(name+'.range_gap')
        bound=self.power(b,n,name+'.range')
        copybase=self.power(b,stride-1,name+'.copybase')
        copyend=self.power(copybase,n,name+'.copylimit')
        copies=self.natural(name+'.copy')
        mask=self.natural(name+'.mask')
        self.equation(name+'.stride_bound',stride-n-1-gap)
        self.equation(name+'.range_bound',u+strict-bound)
        self.equation(name+'.copy_equation',(copybase-1)*copies+1-copyend)
        self.equation(name+'.mask_equation',(b*copybase-1)*mask+1-copyend*bound)
        z=self.meet(u*copies,(b-1)*mask,name+'.select')
        self.interface('spread',name,value=u,base=b,length=n,stride=stride,out=z)
        return z
    def geometric(self,b,n,name):
        s=self.natural(name+'.value')
        end=self.power(b,n,name+'.power')
        self.equation(name+'.equation',(b-1)*s+1-end)
        return s


def specification():
    S=Intended()
    p,q,r,d,e,f=[S.positive('descriptor.'+s) for s in ('p','q','r','d','e','f')]
    tile=S.natural('descriptor.tile')
    patch=S.natural('descriptor.patch')
    zetas={axis:S.natural('target.zeta'+axis) for axis in ('x','y','z')}
    fields=[p-1,q-1,r-1,tile,d-1,e-1,f-1,patch]+list(zetas.values())
    # Independent right-associated ten-pair definition, with code[10]=last field.
    codes={0:S.input-1,10:fields[10]}
    for j in range(1,10):codes[j]=S.natural('descriptor.pair'+str(j))
    for j in range(10):
        combined=fields[j]+codes[j+1]
        S.equation('descriptor.cantor'+str(j),2*codes[j]-combined*combined-combined-2*codes[j+1])

    tile_count=p*q*r
    patch_count=d*e*f
    Tmask=S.geometric(32,tile_count,'tile.mask')
    bits=[S.natural('tile.bit'+str(i)) for i in range(3)]
    for i in range(3):S.subset(Tmask,bits[i],'tile.allow'+str(i))
    S.subset(Tmask,bits[1]+bits[2],'tile.exclude67')
    S.equation('tile.reconstruct',tile-bits[0]-2*bits[1]-4*bits[2])
    Dmask=S.geometric(32,patch_count,'patch.mask')
    S.subset(15*Dmask,patch,'patch.digits')

    K=S.positive('time.layers')
    width=S.positive('radix.width')
    b=S.power(32,width,'radix.base')
    half=S.positive('radix.half')
    growth=S.natural('radix.growth_gap')
    S.equation('radix.half_equation',2*half-b)
    S.equation('radix.growth_equation',b-64*K-64-growth)
    Tb=S.spread(tile,32,tile_count,width,'tile.convert')
    Db=S.spread(patch,32,patch_count,width,'patch.convert')

    tx,ty,tz=[S.positive('box.t'+a)+1 for a in ('x','y','z')]
    hx,hy,hz=p*d*tx,q*e*ty,r*f*tz
    A,B,C=2*hx,2*hy,2*hz
    XY=A*B
    rx_count,ry_count,rz_count=2*d*tx,2*e*ty,2*f*tz
    row=S.power(b,p,'tile.row_radix')
    Trows=S.spread(Tb,row,q*r,rx_count,'tile.rows')
    plane=S.power(b,A*q,'tile.plane_radix')
    Tplanes=S.spread(Trows,plane,r,ry_count,'tile.planes')
    rx=S.geometric(row,rx_count,'tile.repeat_x')
    ry=S.geometric(plane,ry_count,'tile.repeat_y')
    zradix=S.power(b,XY*r,'tile.z_radix')
    rz=S.geometric(zradix,rz_count,'tile.repeat_z')
    background=Tplanes*rx*ry*rz
    prow=S.power(b,d,'patch.row_radix')
    Drows=S.spread(Db,prow,e*f,2*p*tx,'patch.rows')
    pplane=S.power(b,A*e,'patch.plane_radix')
    Dplanes=S.spread(Drows,pplane,f,2*q*ty,'patch.planes')
    shift=S.power(b,hx+A*hy+XY*hz,'patch.shift')
    additions=Dplanes*shift

    X=S.power(b,A,'box.X')
    Y=S.power(X,B,'box.Y')
    Q=S.power(Y,C,'box.Q')
    jx,jy,jz=[S.natural('box.j'+a) for a in ('x','y','z')]
    S.equation('box.jx_equation',b*b*(b-1)*jx+b*b-X)
    S.equation('box.jy_equation',X*X*(X-1)*jy+X*X-Y)
    S.equation('box.jz_equation',Y*Y*(Y-1)*jz+Y*Y-Q)
    I=b*X*Y*jx*jy*jz
    W=S.power(Q,K,'time.endshift')
    R=S.natural('time.repetition')
    S.equation('time.repetition_equation',(Q-1)*R+1-W)
    pre,event,final=[S.natural('time.'+v) for v in ('pre','event','final')]
    S.subset((b-1)*I*R,pre,'time.pre_mask')
    S.subset(I*R,event,'time.event_mask')
    S.subset((b-1)*I,final,'time.final_mask')
    S.equation('time.recurrence',Q*pre+Q*event-pre-W*final)
    nx,ny,nz=[S.natural('time.negative_'+v) for v in ('x','y','z')]
    S.equation('time.div_x',b*nx-pre)
    S.equation('time.div_y',X*ny-pre)
    S.equation('time.div_z',Y*nz-pre)
    available=background*R+additions*R+(b+X+Y)*pre+nx+ny+nz
    selected=S.meet(available,(b-1)*event,'legality.available')
    selected_self=S.meet(pre,(b-1)*event,'legality.self')
    slack=S.natural('legality.slack')
    S.subset((half-1)*event,slack,'legality.slack_mask')
    S.equation('legality.threshold',selected-6*selected_self-6*event-slack)

    locals_={}
    for axis,extent,size in zip(('x','y','z'),(hx,hy,hz),(A,B,C)):
        h=S.natural('target.'+axis+'.halfcode')
        s=S.natural('target.'+axis+'.sign')
        local=S.natural('target.'+axis+'.local')
        gap=S.positive('target.'+axis+'.uppergap')
        S.equation('target.'+axis+'.zigzag',zetas[axis]-2*h-s)
        S.equation('target.'+axis+'.sign_binary',s*s-s)
        S.equation('target.'+axis+'.translate',local-extent-h+2*s*h+s)
        S.equation('target.'+axis+'.bound',local+gap-size)
        locals_[axis]=local
    point=S.power(b,locals_['x']+A*locals_['y']+XY*locals_['z'],'target.point')
    tau=S.natural('target.time')
    timepoint=S.power(Q,tau,'target.timepoint')
    S.subset(event,point*timepoint,'target.fired')

    ports=dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=tile,patch=patch,
        radix=b,radix_width=width,radix_half=half,tile_converted=Tb,patch_converted=Db,
        A=A,B=B,C=C,X=X,Y=Y,Q=Q,half_x=hx,half_y=hy,half_z=hz,
        background=background,additions=additions,interior_mask=I,layers=K,
        endshift=W,repetition=R,pre=pre,event=event,final=final,available=available,
        selected=selected,self_selected=selected_self,legality_slack=slack,
        target_point=point,target_time=tau,target_timepoint=timepoint)
    ports.update({'zeta_'+a:v for a,v in zetas.items()})
    ports.update({'local_'+a:v for a,v in locals_.items()})
    return S,ports


def no_duplicate_keys(pairs):
    out={}
    for k,v in pairs:
        assert k not in out,('duplicate JSON key',k)
        out[k]=v
    return out



def compare_accepted_macro_templates():
    """Recheck the pinned prior DAG's macro polynomials with the SAME specification.

    This is a read of inert prior JSON, never an execution/import of its programs.
    Instantiation parameters are its audited interfaces; all nested equations and
    interfaces are regenerated using our mathematical templates above.
    """
    path=Path('/workspace/shared/sandpile-target-firing-20261004/evidence/polynomial-dag.json')
    pin='352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504'
    raw=path.read_bytes()
    assert sha256(raw).hexdigest()==pin
    old=json.loads(raw,object_pairs_hook=no_duplicate_keys)
    values={'input:InputPlus':Poly.var('input:InputPlus')}
    values.update({'witness:'+w:Poly.var('witness:'+w) for w in old['witnesses']})
    def get(ref):
        if ref.startswith('constant:'):return Poly.integer(int(ref[9:]))
        return values[ref]
    for i,(op,left,right) in enumerate(old['gates'][:old['body_gate_count']]):
        a,b=get(left),get(right)
        values['gate:'+str(i)]=a+b if op=='+' else a-b if op=='-' else a*b
    equations={name:get(left)-get(right) for left,right,name in old['equalities']}
    interfaces={m['name']:m for m in old['macros']}
    checked_clauses=set()
    checked_interfaces=set()
    for name,m in interfaces.items():
        S=Intended()
        kind=m['kind']
        if kind=='power':S.power(get(m['base']),get(m['exponent']),name)
        elif kind=='subset':S.subset(get(m['mask']),get(m['value']),name)
        elif kind=='and':S.meet(get(m['left']),get(m['right']),name)
        elif kind=='spread':S.spread(get(m['value']),get(m['base']),get(m['length']),get(m['stride']),name)
        else:raise AssertionError(('unknown old macro',kind))
        assert S.witnesses<=set(old['witnesses'])
        for clause,expected in S.residuals.items():
            assert equations[clause]==expected,('prior macro residual differs',clause)
            checked_clauses.add(clause)
        for subname,(subkind,ports) in S.macros.items():
            actual=interfaces[subname]
            assert actual['kind']==subkind
            assert set(actual)-{'kind','name'}==set(ports)
            for port,expected in ports.items():
                assert get(actual[port])==expected,('prior macro interface differs',subname,port)
            checked_interfaces.add(subname)
    return dict(source_sha256=pin,macro_interfaces=len(checked_interfaces),
                macro_residuals=len(checked_clauses),matches_same_independent_templates=True)


def main():
    raw=DAG_FILE.read_bytes()
    assert sha256(raw).hexdigest()==FROZEN_SHA256,'Frozen source hash mismatch'
    data=json.loads(raw,object_pairs_hook=no_duplicate_keys)
    assert set(data)=={'schema','input','domain','constants','witnesses','gates','equalities','macros','ports','output','body_gate_count'}
    assert data['schema']=='fixed-positive-integer-polynomial-dag-v1'
    assert data['input']=='InputPlus'
    assert data['domain']=='InputPlus and every witness are positive integers'
    assert data['constants']=='Fixed integer literals are free; every binary arithmetic gate is counted'
    specification_,expected_ports=specification()
    witnesses=data['witnesses']
    assert all(type(w) is str for w in witnesses)
    assert len(set(witnesses))==len(witnesses)
    assert set(witnesses)==specification_.witnesses,'Witness names/adapters differ'
    body=data['body_gate_count']
    gates=data['gates']
    assert type(body) is int and 0<body<=len(gates)
    vals={'input:InputPlus':specification_.input}
    vals.update({'witness:'+w:Poly.var('witness:'+w) for w in witnesses})
    degrees={ref:1 for ref in vals}
    references=set(vals)
    def get(ref):
        assert type(ref) is str
        if ref.startswith('constant:'):
            literal=ref[9:]
            assert re.fullmatch(r'0|-?[1-9][0-9]*',literal),ref
            return Poly.integer(int(literal))
        assert ref in vals,('unknown or forward polynomial reference',ref)
        return vals[ref]
    def deg(ref):
        if ref.startswith('constant:'):return 0
        assert ref in degrees,('unknown or forward degree reference',ref)
        return degrees[ref]
    for i,gate in enumerate(gates):
        assert type(gate) is list and len(gate)==3
        op,a,b=gate
        assert op in ('+','-','*')
        # Validate constants even in the structural sum-of-squares tail.
        for ref in (a,b):
            if ref.startswith('constant:'):get(ref)
            else: assert ref in references,(i,ref)
        ref='gate:'+str(i)
        da,db=deg(a),deg(b)
        degrees[ref]=da+db if op=='*' else max(da,db)
        if i<body:
            pa,pb=get(a),get(b)
            vals[ref]=pa+pb if op=='+' else pa-pb if op=='-' else pa*pb
        references.add(ref)
    eqs=data['equalities']
    names=[q[2] for q in eqs]
    assert len(names)==len(set(names))
    assert set(names)==set(specification_.residuals),'Extra or missing equations'
    residuals={}
    for left,right,name in eqs:
        actual=get(left)-get(right)
        assert actual==specification_.residuals[name],('incorrect residual',name)
        residuals[name]=actual
    assert set(data['ports'])==set(expected_ports)
    for name,ref in data['ports'].items():
        assert get(ref)==expected_ports[name],('incorrect exposed port',name)
    assert len(data['macros'])==len(specification_.macros)
    observed_macro_names=set()
    for macro in data['macros']:
        name,kind=macro['name'],macro['kind']
        assert name not in observed_macro_names,name
        observed_macro_names.add(name)
        assert name in specification_.macros,('extra macro',name)
        ekind,eports=specification_.macros[name]
        assert kind==ekind,(name,kind,ekind)
        assert set(macro)-{'kind','name'}==set(eports),(name,'port keys')
        for port,expression in eports.items():
            assert get(macro[port])==expression,(name,port,'macro port mismatch')
    assert observed_macro_names==set(specification_.macros)
    # Verify literally every post-body gate as the complete ordered SOS.
    cursor=body
    square_refs=[]
    for left,right,name in eqs:
        assert gates[cursor]==['-',left,right],('SOS residual gate',name)
        residual_ref='gate:'+str(cursor)
        cursor+=1
        assert gates[cursor]==['*',residual_ref,residual_ref],('SOS square gate',name)
        square_refs.append('gate:'+str(cursor))
        cursor+=1
    output=square_refs[0]
    for square in square_refs[1:]:
        assert gates[cursor]==['+',output,square],('SOS sum gate',cursor)
        output='gate:'+str(cursor)
        cursor+=1
    assert cursor==len(gates)
    assert output==data['output']
    # Reachability is over the whole literal source, including all unused algebraic terms.
    live=set()
    pending=[output]
    while pending:
        ref=pending.pop()
        if ref in live:continue
        live.add(ref)
        if ref.startswith('gate:'):pending.extend(gates[int(ref[5:])][1:])
    assert 'input:InputPlus' in live
    assert all('witness:'+w in live for w in witnesses)
    assert all('gate:'+str(i) in live for i in range(len(gates)))
    # Exact source degree: all squares have degree <=2d, and the sum of their
    # highest homogeneous squares is explicitly normalized and nonzero.
    max_degree=max(p.degree() for p in residuals.values())
    top={name:p.top() for name,p in residuals.items() if p.degree()==max_degree}
    homogeneous=Poly.integer(0)
    for p in top.values(): homogeneous+=p*p
    assert homogeneous.degree()==2*max_degree
    assert degrees[output]==18
    assert max_degree==9 and homogeneous.degree()==18
    expected_counts={'positive_witnesses':3865,'equations':2251,'gates':17275,'ports':44}
    actual_counts=dict(positive_witnesses=len(witnesses),equations=len(eqs),gates=len(gates),ports=len(data['ports']))
    assert actual_counts==expected_counts
    macro_counts=Counter(m['kind'] for m in data['macros'])
    assert dict(macro_counts)=={'power':138,'subset':34,'and':8,'spread':6}
    report=dict(
        verdict='PASS',source_sha256=FROZEN_SHA256,
        accepted_macro_compatibility=compare_accepted_macro_templates(),
        builder_sha256=sha256((ROOT/'build_repeated_certificate.py').read_bytes()).hexdigest(),
        checker_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        exact_verified_counts=actual_counts,
        verified_macro_interfaces=len(observed_macro_names),macro_counts=dict(macro_counts),
        body_gate_count=body,body_gate_operations=dict(Counter(g[0] for g in gates[:body])),
        sos_gate_operations=dict(Counter(g[0] for g in gates[body:])),
        all_gate_operations=dict(Counter(g[0] for g in gates)),
        exact_residual_degree=max_degree,syntactic_source_degree_upper_bound=degrees[output],
        exact_total_degree=homogeneous.degree(),
        degree_nine_residuals={name:p.text() for name,p in top.items()},
        highest_homogeneous_part=homogeneous.text(),
        degree_histogram=dict(sorted(Counter(p.degree() for p in residuals.values()).items())),
        all_input_witness_and_gate_leaves_live=True,complete_ordered_sum_of_squares_verified=True,
        max_sparse_body_gate_terms=max(len(p.terms) for p in vals.values()),
        forbidden_programs_executed_or_imported=False,
    )
    assert sha256(DAG_FILE.read_bytes()).hexdigest()==FROZEN_SHA256
    (HERE/'receipt.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report,sort_keys=True,indent=2))

if __name__=='__main__':main()
