"""Paid fixed-source/mass/horizon endpoint compiler for the NEW parallel rule.
No F-template array or coordinate bound. All loops depend on source, n and T.
Only the pinned source parser is reused; no frozen transition is called here.
"""
from pathlib import Path
from hashlib import sha256
from types import ModuleType
import sys
from itertools import combinations
from circuit import Circuit, const, var, add, sub, mul, ev, dump

FROZEN = Path(__file__).resolve().parent
PINS = {'frozen_lazy_source.py':'42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61',
        'frozen_reversible_binary.py':'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f'}
for name, pin in PINS.items():
    if sha256((FROZEN/name).read_bytes()).hexdigest()!=pin: raise RuntimeError(('pin mismatch',name))
_parser = ModuleType('_certificate_pinned_parser'); _parser.__file__=str(FROZEN/'frozen_lazy_source.py')
sys.modules[_parser.__name__]=_parser
exec(compile((FROZEN/'frozen_lazy_source.py').read_bytes(),_parser.__file__,'exec'),_parser.__dict__)

class Emitter:
    def __init__(self, circuit, metadata):
        self.c=circuit;self.m=metadata;self.block_reports=[]
    def plus(self,x,k):return add(x,const(k))
    def times(self,x,k):return mul(x,const(k))
    def guard(self,X,u,table):
        c,m=self.c,self.m; classes=[];valid=[]
        for side in (-1,1):
            if side==-1:lo,hi=self.plus(u,-m.Z-m.J),self.plus(u,-m.Z)
            else:lo,hi=self.plus(u,m.Z),self.plus(u,m.Z+m.J)
            flags=[c.interval(x,lo,hi) for x in X]
            count=c.integer(sum_poly(flags));valid.append(c.le(count,const(1)))
            # Zero hits -> J+1; singleton -> its distance from the inner endpoint.
            terms=[c.integer(mul(f,self.plus(self.times(sub(x,u),side),-m.Z))) for f,x in zip(flags,X)]
            offset=c.integer(sum_poly(terms))
            singleton=c.eq(count,const(1))
            classes.append(c.select(singleton,const(m.J+1),offset))
        # Literal truth-table scan is charged at every entry, including false cells.
        choices=[]
        for i,row in enumerate(table):
            for j,value in enumerate(row):
                choices.append(c.all((c.eq(classes[0],const(i)),c.eq(classes[1],const(j)),const(int(value)))))
        return c.AND(c.all(valid),c.any(choices))
    def raw(self,X,block):
        c,m=self.c,self.m;n=len(X);out=[]
        es,em,pm,r=4*m.D+15,2*m.D+6,2*m.D+7,m.D+3
        def put(ID,u,old,new,B,conditions,table=None,label=0,family=''):
            flags=[c.interval(x,self.plus(u,-3*B-1),self.plus(u,3*B+1)) for x in X]
            count=c.integer(sum_poly(flags))
            predicates=list(conditions)+[c.eq(count,const(len(old))) ]
            if table is not None:predicates.append(self.guard(X,u,table))
            raw=c.all(predicates)
            # Pairs have a fixed, fully defined padding endpoint with zero move.
            old=tuple(old)+(const(0),)*(3-len(old));new=tuple(new)+(const(0),)*(3-len(new))
            out.append(dict(raw=raw,ID=ID,u=u,old=old,new=new,arity=const(2 if B==m.B2 else 3),label=label,family=family))
        def pair_new(head,gap,marker=None):
            return (head,self.plus(head,gap)) if marker is None else (head,self.plus(head,gap),marker)
        for i,j in combinations(range(n),2):
            h,h2=X[i],X[j];gap=c.sub(h2,h)
            markers=[X[k] for k in range(n) if k not in (i,j)]
            for eidx,e in enumerate(m.moving):
                for kindno,kind in enumerate(('O','I')):
                    w=e.side if kind=='O' else -e.side
                    eb=eidx*es+kindno*em;pb=m.E_count+(2*eidx+kindno)*pm
                    for ell in (0,1):
                        g=m._gap(kind,eidx,'-' if ell else '+');gn=m._gap(kind,eidx,'+' if ell else '-')
                        gapok=c.eq(gap,const(g))
                        if block=='E':
                            u=self.plus(h,-ell*w);hn=self.plus(h,(1-2*ell)*w)
                            put(const(eb),u,(h,h2),pair_new(hn,gn),m.B2,[gapok],label=ell,family='free')
                        else:
                            put(const(pb),h,(h,h2),pair_new(h,gn),m.B2,[gapok],label=ell,family='phase-free')
                        for z in markers:
                            distance=c.sub(h,z)
                            if block=='E':
                                t0=self.plus(self.times(distance,w),-ell)
                                ok=c.interval(t0,const(m.S),const(m.L))
                                t=c.select(ok,const(m.S),t0)
                                ID=c.integer(self.plus(t,eb+1-m.S))
                                put(ID,z,(h,h2,z),pair_new(self.plus(h,(1-2*ell)*w),gn,z),m.B3,[gapok,ok],label=ell,family='behind')
                                t0=self.plus(self.times(distance,-w),ell)
                                ok=c.interval(t0,const(m.S+1),const(m.L));t=c.select(ok,const(m.S+1),t0)
                                ID=c.integer(self.plus(t,eb+1+r-m.S-1))
                                put(ID,z,(h,h2,z),pair_new(self.plus(h,(1-2*ell)*w),gn,z),m.B3,[gapok,ok],label=ell,family='ahead')
                            else:
                                for side in (-1,1):
                                    t0=self.times(distance,side);ok=c.interval(t0,const(m.S),const(m.L))
                                    t=c.select(ok,const(m.S),t0)
                                    ID=c.integer(self.plus(t,pb+1+(0 if side==-1 else r)-m.S))
                                    put(ID,z,(h,h2,z),pair_new(h,gn,z),m.B3,[gapok,ok],label=ell,family='phase-near')
                if block=='E':
                    v=e.side;qi=m.control_index[e.source];qj=m.control_index[e.target]
                    for z in markers:
                        distance=c.sub(h,z)
                        for ell in (0,1):
                            base=eidx*es+2*em
                            # Dispatch: home+ at +S <-> O- at vS.
                            g=m._gap('O',eidx,'-') if ell else m._gap('H',qi,'+')
                            gn=m._gap('H',qi,'+') if ell else m._gap('O',eidx,'-')
                            hp=(v if ell else 1)*m.S;hn=self.plus(z,(1 if ell else v)*m.S)
                            put(const(base),z,(h,h2,z),pair_new(hn,gn,z),m.B3,[c.eq(gap,const(g)),c.eq(distance,const(hp))],e.domain_table,ell,'dispatch')
                            # Endpoint: reverse anchor is z-v*delta.
                            u=self.plus(z,-ell*v*e.delta)
                            g=m._gap('I',eidx,'-') if ell else m._gap('O',eidx,'+')
                            gn=m._gap('O',eidx,'+') if ell else m._gap('I',eidx,'-')
                            shift=(1-2*ell)*v*e.delta
                            put(const(base+1),u,(h,h2,z),pair_new(self.plus(h,shift),gn,self.plus(z,shift)),m.B3,[c.eq(gap,const(g)),c.eq(distance,const(-v*m.S))],label=ell,family='endpoint')
                            # Commit always uses the branch image table.
                            g=m._gap('H',qj,'-') if ell else m._gap('I',eidx,'+')
                            gn=m._gap('I',eidx,'+') if ell else m._gap('H',qj,'-')
                            hp=(1 if ell else v)*m.S;hn=self.plus(z,(v if ell else 1)*m.S)
                            put(const(base+2),z,(h,h2,z),pair_new(hn,gn,z),m.B3,[c.eq(gap,const(g)),c.eq(distance,const(hp))],e.image_table,ell,'commit')
            if block=='E':
                for eidx,e in enumerate(m.direct):
                    qi=m.control_index[e.source];qj=m.control_index[e.target]
                    for z in markers:
                        for ell in (0,1):
                            g=m._gap('H',qj,'-') if ell else m._gap('H',qi,'+')
                            gn=m._gap('H',qi,'+') if ell else m._gap('H',qj,'-')
                            put(const(m.p*es+eidx),z,(h,h2,z),pair_new(h,gn,z),m.B3,[c.eq(gap,const(g)),c.eq(sub(h,z),const(m.S))],e.domain_table,ell,'direct')
            else:
                for qi in range(m.m):
                    for z in markers:
                        for ell in (0,1):
                            g=m._gap('H',qi,'-' if ell else '+');gn=m._gap('H',qi,'+' if ell else '-')
                            put(const(m.E_count+2*m.p*pm+qi),z,(h,h2,z),pair_new(h,gn,z),m.B3,[c.eq(gap,const(g)),c.eq(sub(h,z),const(m.S))],label=ell,family='phase-home')
        expected=n*(n-1)//2*(4*m.p+((14*m.p+2*m.a) if block=='E' else (8*m.p+2*m.m))*max(n-2,0))
        if len(out)!=expected:raise RuntimeError(('slot width',block,len(out),expected))
        return out
    def sort_coordinates(self,X):
        c=self.c;Y=list(X)
        # Odd-even transposition sorting network, fixed n phases.
        for phase in range(len(Y)):
            for j in range(phase%2,len(Y)-1,2):
                swap=c.ge(Y[j],self.plus(Y[j+1],1));a,b=Y[j],Y[j+1]
                Y[j],Y[j+1]=c.select(swap,a,b),c.select(swap,b,a)
        return Y
    def sort_keys(self,raw):
        c=self.c;N=1
        while N<len(raw):N*=2
        rows=[(r['raw'],r['u'],const(i)) for i,r in enumerate(raw)]
        rows +=[(const(0),const(0),const(-1))]*(N-len(rows))
        def less(a,b):
            # Live keys first, then increasing anchor. Ties don't swap.
            live=c.AND(a[0],c.NOT(b[0]))
            same=c.eq(a[0],b[0]);anchor=c.ge(b[1],self.plus(a[1],1))
            return c.OR(live,c.AND(same,anchor))
        k=2
        while k<=N:
            j=k//2
            while j:
                for i in range(N):
                    other=i^j
                    if other>i:
                        a,b=rows[i],rows[other]
                        swap=less(b,a) if i&k==0 else less(a,b)
                        rows[i]=tuple(c.select(swap,x,y) for x,y in zip(a,b))
                        rows[other]=tuple(c.select(swap,y,x) for x,y in zip(a,b))
                j//=2
            k*=2
        return rows
    def lanes(self,raw,n,H):
        c=self.c
        if not raw:return []
        sorted_keys=self.sort_keys(raw);isolated=[]
        for j,(live,u,idx) in enumerate(sorted_keys):
            bad=[]
            if j:bad.append(c.AND(sorted_keys[j-1][0],c.le(sub(u,sorted_keys[j-1][1]),const(H))))
            if j+1<len(sorted_keys):bad.append(c.AND(sorted_keys[j+1][0],c.le(sub(sorted_keys[j+1][1],u),const(H))))
            isolated.append(c.AND(live,c.NOT(c.any(bad))))
        ranks=[];rank=const(0)
        for flag in isolated:ranks.append(rank);rank=c.integer(add(rank,flag))
        lanes=[]
        for k in range(n//2):
            present=c.ge(rank,const(k+1));idx=const(-1)
            for row,flag,rank_before in zip(sorted_keys,isolated,ranks):
                route=c.AND(flag,c.eq(rank_before,const(k)))
                idx=c.select(route,idx,row[2])
            lane=dict(present=present,ID=const(0),u=const(0),arity=const(0),old=[const(0)]*3,new=[const(0)]*3)
            for i,r in enumerate(raw):
                route=c.AND(present,c.eq(idx,const(i)))
                for field in ('ID','u','arity'):lane[field]=c.select(route,lane[field],r[field])
                for field in ('old','new'):
                    lane[field]=[c.select(route,a,b) for a,b in zip(lane[field],r[field])]
            lanes.append(lane)
        return lanes
    def move(self,X,lanes,flags):
        c=self.c;Y=[]
        for x in X:
            terms=[]
            for lane,selected in zip(lanes,flags):
                for j,(old,new) in enumerate(zip(lane['old'],lane['new'])):
                    hit=c.all((selected,c.ge(lane['arity'],const(j+1)),c.eq(x,old)))
                    terms.append(c.integer(mul(hit,sub(new,old))))
            Y.append(c.integer(add(x,sum_poly(terms))))
        return self.sort_coordinates(Y)
    def block(self,X,name):
        c,m=self.c,self.m;start=c.ledger();raw=self.raw(X,name)
        r=m.Z+m.J if name=='E' else 3*m.B3+1;q=m.B3+r;H=2*q
        lanes=self.lanes(raw,len(X),H);selected=[]
        for lane in lanes:
            Y=self.move(X,[lane],[lane['present']]);after=self.raw(Y,name)
            own=[];other=[]
            for a in after:
                near=c.interval(a['u'],self.plus(lane['u'],-q),self.plus(lane['u'],q))
                same=c.AND(c.eq(a['ID'],lane['ID']),c.eq(a['u'],lane['u']))
                relevant=c.AND(a['raw'],near)
                own.append(c.AND(relevant,same));other.append(c.AND(relevant,c.NOT(same)))
            selected.append(c.all((lane['present'],c.any(own),c.NOT(c.any(other)))))
        Y=self.move(X,lanes,selected) if lanes else list(X)
        end=c.ledger();self.block_reports.append(dict(name=name,slots=len(raw),lanes=len(lanes),delta={k:end.get(k,0)-start.get(k,0) for k in ('A','G','I','Q','witnesses','residuals','residual_monomials','ordered_sos_term_bound')}))
        return Y,raw,lanes,selected

def sum_poly(items):
    out={}
    for x in items:out=add(out,x)
    return out

def natural_pairs(coords):return [v for x in coords for v in (max(x,0),max(-x,0))]

class Certificate:
    def __init__(self,source,n,T,inverse=False):
        if type(n)is not int or n<0 or type(T)is not int or T<0 or type(inverse)is not bool:raise ValueError('n,T natural; inverse bool')
        self.n,self.T,self.inverse=n,T,inverse;self.metadata=_parser.compile_lazy_source(source)
        self.circuit=Circuit([f'{side}_{i}_{sign}' for side in ('x','y') for i in range(n) for sign in ('plus','minus')])
        c=self.circuit;self.emitter=Emitter(c,self.metadata);X=[];target=[]
        for side,arr in enumerate((X,target)):
            for i in range(n):
                p,v=var(2*(side*n+i)),var(2*(side*n+i)+1);c.check(mul(p,v));arr.append(sub(p,v))
            for i in range(n-1):c.check(sub(c.ge(arr[i+1],add(arr[i],const(1))),const(1)))
        self.input=X;self.target=target;self.traces=[]
        for _ in range(T):
            for name in (('P','E') if inverse else ('E','P')):
                X,raw,lanes,selected=self.emitter.block(X,name);self.traces.append((name,raw,lanes,selected,X))
        self.output=X
        for x,y in zip(X,target):c.check(sub(x,y))
    def witness(self,x,y,check=True):
        if len(x)!=self.n or len(y)!=self.n:raise ValueError('mass mismatch')
        return self.circuit.evaluate(natural_pairs(x)+natural_pairs(y),check=check)
    def result(self,x):
        values=self.witness(x,[0]*self.n,check=False)
        return tuple(ev(p,values) for p in self.output)
    def ledger(self):
        m=self.metadata
        return dict(n=self.n,T=self.T,inverse=self.inverse,source=m.ledger(),
            new_rule_radius=180*m.D+258+9*m.J,legacy_ordered_radius=m.radius,
            endpoint_type_count=m.factors,
            source_metadata_semantics={'radius':'legacy ordered rule radius, not the new CA radius',
                'factors':'endpoint template types, not emitted arithmetic operations',
                'particles':'source encoding uses five particles; certificate mass is n'},
            circuit=self.circuit.ledger(),blocks=self.emitter.block_reports)
    def polynomial(self):return self.circuit.expanded()
    def serialize(self):
        return dict(format='natural-quartic-sos-v1',input_count=self.circuit.input_count,variable_names=self.circuit.names,residuals=[dump(r) for r in self.circuit.rows],ledger=self.ledger())
