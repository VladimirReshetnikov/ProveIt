#!/usr/bin/env python3
"""Independent whole-polynomial, restoration, and arithmetic graph audit.

Reads candidate JSON as inert data. Does not import or execute its builder,
exporter, checkers, or any upstream code. Checks use explicit exceptions.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path

def need(x, why):
    if not x: raise ValueError(why)

def clean(p): return {m:c for m,c in p.items() if c}
def add(*ps):
    r=collections.defaultdict(int)
    for p in ps:
        for m,c in p.items(): r[m]+=c
    return clean(r)
def scale(p,n): return clean({m:c*n for m,c in p.items()})
def sub(p,q): return add(p,scale(q,-1))
def mul(*ps):
    r={():1}
    for p in ps:
        s=collections.defaultdict(int)
        for m,c in r.items():
            for n,d in p.items():s[tuple(sorted(m+n))]+=c*d
        r=clean(s)
    return r
def num(n):return {} if n==0 else {():n}
def vv(i):return {(i,):1}
def sparse(t):
    p={tuple(m):c for c,m in t}
    need(len(p)==len(t) and all(c and list(m)==sorted(m) for c,m in t),'noncanonical sparse polynomial')
    return p
def key(p):return tuple(sorted(p.items()))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

class Audit:
    def __init__(self,path):
        self.path=path
        self.c=json.loads((path/'circuit.json').read_text())
        self.e=json.loads((path/'equation.json').read_text())
        self.p=json.loads((path/'expanded_polynomial.json').read_text())
        self.vars=self.c['variables'];self.names={v['name']:i for i,v in enumerate(self.vars)}
        need(len(self.names)==len(self.vars),'duplicate raw variable name')
        self.rows=self.c['residuals']
        self.named={r['label']:sparse(r['terms']) for r in self.rows if r['gate'] is None}
        need(len(self.named)==sum(r['gate'] is None for r in self.rows),'duplicate semantic row')
        self.gates={r['gate']:sparse(r['terms']) for r in self.rows if r['gate'] is not None}
        self.gate_ops={r['gate']:r['label'] for r in self.rows if r['gate'] is not None}
        self.macro=self.c['macros'];self.binding=self.c['bindings'];self.counts={}
        self.power_lookup={(tuple(m['base']),tuple(m['exponent'])):m['output'] for m in self.macro if m['kind']=='power'}
        self.binom_lookup={(tuple(m['n']),tuple(m['k'])):m['output'] for m in self.macro if m['kind']=='binomial'}
        self.fact_lookup={tuple(m['n']):m['output'] for m in self.macro if m['kind']=='factorial'}
    def v(self,name):return vv(self.names[name])
    def atom(self,a):return num(a[1]) if a[0]=='c' else vv(a[1])
    def gate_rhs(self,i):
        p=self.gates[i]
        need(p.get((i,))==1 and all(i not in m for m in p if m!=(i,)),'nonmonic gate')
        rhs=scale({m:c for m,c in p.items() if m!=(i,)},-1)
        need(all(c>0 and all(j<i for j in m) for m,c in rhs.items()),'invalid natural triangular gate')
        return rhs
    def expander(self,cut=()):
        stop={a[1] for a in cut if a[0]=='v'};cache={}
        def variable(i):
            if i not in cache:
                cache[i]=vv(i) if i in stop or i not in self.gates else poly(self.gate_rhs(i))
            return cache[i]
        def poly(p):return add(*(scale(mul(*(variable(i) for i in mon)),c) for mon,c in p.items()))
        def atom(a):return num(a[1]) if a[0]=='c' else variable(a[1])
        return poly,atom
    def check_gates(self):
        for i in self.gates:self.gate_rhs(i)
        for r in self.rows:
            need(all(len(m)<=2 and all(0<=i<len(self.vars) for i in m) for _,m in r['terms']),'invalid raw residual')
        self.counts['raw_gates']=len(self.gates)
    def check_restoration(self):
        final_names=[v['name'] for v in self.e['variables']]
        need(len(final_names)==len(set(final_names)),'duplicate final variable')
        ren={self.names[n]:j for j,n in enumerate(final_names)}
        replacement={};gone=0
        for i in range(len(self.vars)):
            if i in ren:replacement[i]=vv(ren[i]);continue
            need(i in self.gates,'semantic coordinate lost')
            rhs=self.gate_rhs(i)
            need(all(len(m)<=1 for m in rhs),'nonaffine coordinate removed')
            value=add(*(scale(mul(*(replacement[j] for j in m)),c) for m,c in rhs.items()))
            need(all(c>=0 and len(m)<=1 for m,c in value.items()),'restoration not natural affine')
            replacement[i]=value;gone+=1
        expect=[]
        for r in self.rows:
            value=add(*(scale(mul(*(replacement[j] for j in m)),c) for c,m in r['terms']))
            if value:expect.append((r['label'],key(value)))
        actual=[(r['label'],key(sparse(r['terms']))) for r in self.e['residuals']]
        need(collections.Counter(expect)==collections.Counter(actual),'whole affine row restoration mismatch')
        self.counts['exact_affine_rows']=len(actual);self.counts['restored_affine_coordinates']=gone
    def check_expansion(self):
        P=collections.defaultdict(int);used=set()
        for r in self.e['residuals']:
            q=sparse(r['terms']);need(all(len(m)<=2 for m in q),'nonquadratic exported residual')
            used.update(i for m in q for i in m)
            for mon,coef in mul(q,q).items():P[mon]+=coef
        P=clean(P)
        need(P==sparse(self.p['terms']),'full SOS coefficient mismatch')
        n=len(self.e['variables'])
        need(used==set(range(n)) and self.p['variable_count']==n,'unused or invalid variable')
        metrics={'natural_variables':n,'quadratic_residuals':len(self.e['residuals']),'degree':max(map(len,P)),
                 'monomials':len(P),'coefficient_height':max(map(abs,P.values()))}
        need(metrics['degree']==4,'degree is not exactly four')
        need(all(self.e['metrics'][k]==v for k,v in metrics.items()),'metric mismatch')
        self.counts['polynomial']=metrics
    def check_powers(self):
        count=0
        for m in self.macro:
            if m['kind']!='power':continue
            tag=m['tag'];expand,at=self.expander([m['base'],m['exponent']]);n,k=map(at,[m['base'],m['exponent']])
            V=lambda x:self.v(tag+'.'+x)
            if m.get('parametric'):
                out=at(m['output']);one=num(1);X,U=V('X'),V('U')
                qB,qS,qR,qP=[V(s) for s in ['B_mod_U.quotient','S_mod_U.quotient','R_mod_4Y.quotient','power_mod_T.quotient']]
                need(list(map(at,m['quotients']))==[qB,qS,qR,qP],'parametric quotient binding')
                A=add(V('a2'),num(2));Y=add(k,V('yk'));T=add(out,V('gap'),one)
                pv=mul(Y,Y,add(V('vd'),one));B=add(one,mul(num(4),Y,add(V('q4_minus_one'),one)))
                integer=self.binding.get('integer_template',False)
                S=V('S') if integer else add(X,mul(U,qS));R=V('R') if integer else add(k,mul(num(4),Y,qR))
                coords={'A':A,'Y':Y,'T':T,'V':pv,'B':B,'S':S,'R':R,'X':X,'U':U}
                need({name:at(a) for name,a in m['arithmetic_coordinates'].items()}==coords,'parametric coordinate substitution')
                def norm(a,x,y):return sub(add(mul(x,x),mul(y,y)),add(one,mul(a,a,y,y)))
                W=add(n,k)
                expected={'norm_AXY':norm(A,X,Y),'norm_AUV':norm(A,U,pv),'norm_BSR':norm(B,S,R),
                          'B_mod_U':sub(B,add(A,mul(U,qB))),
                          'power_mod_T':sub(add(X,mul(Y,n)),add(mul(Y,A),out,mul(T,qP))),
                          'T_definition':sub(mul(num(2),A,n),add(T,mul(n,n),one)),
                          'last_norm':norm(add(W,one),A,mul(W,V('Z')))}
                if integer:
                    expected['S_definition']=sub(S,add(X,mul(U,qS)))
                    expected['R_definition']=sub(R,add(k,mul(num(4),Y,qR)))
                actual={s[len(tag)+1:]:expand(p) for s,p in self.named.items() if s.startswith(tag+'.')}
                need(actual==expected,'parametric positive-power graph mismatch '+tag)
                count+=1;continue
            A,T,Z,X,Y,U,Vv,S,R,B=map(V,['A','T','Z','X','Y','U','V','S','R','B'])
            out=at(m['output']);one=num(1);W=add(n,k)
            def norm(a,x,y):return sub(add(mul(x,x),mul(y,y)),add(one,mul(a,a,y,y)))
            expected={'A_ge_2':sub(A,add(V('a2'),num(2))),
                      'Y_ge_k':sub(Y,add(k,V('yk'))),'B_ge_2':sub(B,add(V('b2'),num(2))),
                      'norm_AXY':norm(A,X,Y),'norm_AUV':norm(A,U,Vv),'norm_BSR':norm(B,S,R),
                      'B_mod_4Y':sub(B,add(one,mul(num(4),Y,V('q4')))),
                      'V_positive_multiple':sub(Vv,mul(Y,Y,add(V('vd'),one))),
                      'T_definition':sub(mul(num(2),A,n),add(T,mul(n,n),one)),
                      'output_bound':sub(T,add(out,V('gap'),one)),
                      'last_norm':norm(add(W,one),A,mul(W,Z))}
            for label,left,right,mod in [('B_mod_U',B,A,U),('S_mod_U',S,X,U),('R_mod_4Y',R,k,mul(num(4),Y))]:
                record=next(q for q in self.macro if q['kind'] in ('congruence','forward_congruence') and q['label']==tag+'.'+label)
                need(at(record['left'])==left and at(record['right'])==right and at(record['modulus'])==mod,'Pell congruence binding')
                if record['kind']=='forward_congruence':
                    expected[label+'.forward']=sub(left,add(right,mul(mod,at(record['quotient']))))
                else:
                    qp,qm=at(record['positive_left_quotient']),at(record['positive_right_quotient'])
                    expected[label]=sub(add(left,mul(mod,qp)),add(right,mul(mod,qm)))
            if tag+'.power_nonnegative_quotient' in self.names:
                expected['power_oriented']=sub(add(X,mul(Y,n)),add(mul(Y,A),out,mul(T,V('power_nonnegative_quotient'))))
            else:
                record=next(q for q in self.macro if q['kind']=='congruence' and q['label']==tag+'.power_mod_T')
                qp,qm=at(record['positive_left_quotient']),at(record['positive_right_quotient'])
                expected['power_mod_T']=sub(add(X,mul(Y,n),mul(T,qp)),add(mul(Y,A),out,mul(T,qm)))
            actual={s[len(tag)+1:]:expand(p) for s,p in self.named.items() if s.startswith(tag+'.')}
            need(actual==expected,'exact power graph mismatch: '+tag)
            count+=1
        self.counts['exact_positive_power_graphs']=count
    def check_congruences(self):
        n=0;offsets=set()
        for m in self.macro:
            if m['kind']=='integer_congruence':
                atoms=[m[k] for k in ['left','right','modulus','quotient']]
                exp,at=self.expander(atoms);l,r,d,q=map(at,atoms)
                need(exp(self.named[m['label']+'.integer'])==sub(l,add(r,mul(d,q))),'integer quotient graph')
            if m['kind']!='congruence':continue
            atoms=[m[k] for k in ['left','right','modulus','positive_left_quotient','positive_right_quotient']]
            exp,at=self.expander(atoms);l,r,d,qp,qm=map(at,atoms)
            need(exp(self.named[m['label']])==sub(add(l,mul(d,qp)),add(r,mul(d,qm))),'signed quotient graph')
            offsets.add(tuple(m['positive_left_quotient']));n+=1
        if not offsets:
            need('unrestricted_integer_quotients' in self.binding,'missing signed congruences')
            self.counts['exact_shared_offset_congruences']=0;return
        need(len(offsets)==1,'not exactly one shared signed offset')
        offset=next(iter(offsets))[1]
        def depends(i,seen=None):
            if i==offset:return True
            if i not in self.gates:return False
            if seen is None:seen=set()
            if i in seen:return False
            seen.add(i)
            return any(depends(j,seen) for mon in self.gate_rhs(i) for j in mon)
        for m in self.macro:
            keys={'power':['base','exponent'],'binomial':['n','k'],'factorial':['n']}.get(m['kind'],[])
            for k in keys:
                a=m[k];need(a[0]=='c' or not depends(a[1]),'shared offset enters arithmetic macro input')
        need(not depends(self.binding['H'][1]),'shared offset enters majorant')
        self.counts['exact_shared_offset_congruences']=n
    def check_compositions(self):
        rhs_lookup={key(self.gate_rhs(i)):['v',i] for i in self.gates}
        def atom_for(p):
            if not p:return ['c',0]
            if len(p)==1:
                mon,c=next(iter(p.items()))
                if not mon:return ['c',c]
                if len(mon)==1 and c==1:return ['v',mon[0]]
            need(key(p) in rhs_lookup,'missing arithmetic composition gate')
            return rhs_lookup[key(p)]
        def plus(a,b):return atom_for(add(self.atom(a),self.atom(b)))
        def times(a,b):return atom_for(mul(self.atom(a),self.atom(b)))
        one,two=['c',1],['c',2]
        def power(a,b):
            need((tuple(a),tuple(b)) in self.power_lookup,'missing licensed power call')
            return self.power_lookup[(tuple(a),tuple(b))]
        def choose(a,b):
            need((tuple(a),tuple(b)) in self.binom_lookup,'missing licensed binomial call')
            return self.binom_lookup[(tuple(a),tuple(b))]
        nb=nf=0
        for m in self.macro:
            if m['kind']=='binomial':
                n,k,out=m['n'],m['k'],m['output'];tag=self.vars[out[1]]['name'].split('.')[0]
                q=plus(power(two,n),one);numr=power(plus(q,one),n);den=power(q,k)
                exp,at=self.expander([q,numr,den]);Q,A,D=map(at,[q,numr,den]);V=lambda s:self.v(tag+'.'+s)
                expected={'digit_division':sub(A,add(mul(D,add(mul(Q,V('high')),at(out))),V('remainder'))),
                          'remainder_bound':sub(D,add(V('remainder'),V('rslack'),num(1))),
                          'digit_bound':sub(Q,add(at(out),V('oslack'),num(1)))}
                actual={s[len(tag)+1:]:exp(p) for s,p in self.named.items() if s.startswith(tag+'.')}
                need(actual==expected,'binomial graph mismatch '+tag);nb+=1
            elif m['kind']=='factorial':
                n,out=m['n'],m['output'];tag=self.vars[out[1]]['name'].split('.')[0]
                shift=plus(n,two);radius=power(shift,shift);c=choose(plus(radius,n),n);numr=power(plus(radius,one),n)
                exp,at=self.expander([c,numr]);C,A=map(at,[c,numr]);V=lambda s:self.v(tag+'.'+s)
                expected={'ceiling':sub(add(A,C),add(mul(C,at(out)),V('remainder'),num(1))),
                          'remainder_bound':sub(C,add(V('remainder'),V('slack'),num(1)))}
                actual={s[len(tag)+1:]:exp(p) for s,p in self.named.items() if s.startswith(tag+'.')}
                need(actual==expected,'factorial graph mismatch '+tag);nf+=1
        b=self.binding;N=b['parameters']['t'];T=b['factorial'];H=b['H'];B=b['CRT_product']
        need(self.fact_lookup[tuple(H)]==T,'factorial-majorant binding')
        Q=plus(power(plus(times(plus(N,one),T),one),N),two)
        tn=power(T,N);nfact=self.fact_lookup[tuple(N)];ch=choose(plus(Q,N),N)
        exp,at=self.expander([N,T,Q,tn,nfact,ch]);Tv,Qv,Bv=at(T),at(Q),at(B)
        mod=self.v('CRT.product.modulus');q=self.v('CRT.product.quotient');slack=self.v('CRT.product.slack')
        neg=b.get('negative_moduli',False)
        expected={'modulus_definition':sub(mod,add(mul(Tv,Qv),num(1))) if neg else sub(add(mod,num(1)),mul(Tv,Qv)),
                  'division':sub(mul(at(tn),at(nfact),at(ch)),add(mul(mod,q),Bv)),
                  'remainder_bound':sub(mod,add(Bv,slack,num(1)))}
        actual={s[len('CRT.product.'):]:exp(p) for s,p in self.named.items() if s.startswith('CRT.product.')}
        need(actual==expected,'CRT product formula mismatch')
        # Verify every range binomial and the encoded index/evaluation bindings.
        for name,A in b['encoded_columns'].items():
            ch=choose(A,b['range_lower_arguments'][name]);ex,at=self.expander([ch,B])
            need(ex(self.named['CRT.range.'+name])==sub(at(ch),mul(at(B),self.v('CRT.range_quotient.'+name))),'CRT range binding')
        ex,at=self.expander([b['encoded_index'],T,B]);idx=at(b['encoded_index']);qi=self.v('CRT.index_quotient')
        lhs=mul(add(idx,num(1)),at(T));rhs=mul(at(B),qi)
        expected=sub(lhs,add(rhs,num(1))) if neg else sub(add(lhs,num(1)),rhs)
        need(ex(self.named['CRT.index_constraint'])==expected,'CRT index sign/binding')
        m=next(m for m in self.macro if m['kind'] in ('congruence','integer_congruence') and m['label']=='CRT.evaluation')
        need(m['left']==b['encoded_E'] and m['right']==b['encoded_F'] and m['modulus']==B,'encoded row evaluation binding')
        carrier=power(plus(b['parameters']['m'],one),N)
        ex,at=self.expander([carrier,b['parameters']['M0']])
        need(ex(self.named['carrier_power'])==sub(at(carrier),add(at(b['parameters']['M0']),num(1))),'carrier power binding')
        self.counts['exact_binomial_graphs']=nb;self.counts['exact_factorial_graphs']=nf;self.counts['exact_CRT_product_and_range_bindings']=True
    def check_positivity(self):
        certified={};records=[]
        def lower(a,cache):
            if a[0]=='c':return min(1,a[1])
            i=a[1]
            if i in certified:return certified[i]
            if i in cache:return cache[i]
            if i not in self.gates:return 0
            p=self.gate_rhs(i);value=0
            for mon,c in p.items():
                term=min(1,c)
                for j in mon:term*=lower(['v',j],cache)
                value=min(1,value+term)
            cache[i]=value;return value
        for m in self.macro:
            if m['kind']=='power':
                n,k=lower(m['base'],{}),lower(m['exponent'],{})
                need(n==k==1,'unlicensed positive-power specialization: '+m['tag'])
                certified[m['output'][1]]=1;records.append(m['tag'])
            elif m['kind']=='factorial':
                need(lower(m['n'],{})==1,'nonpositive specialized factorial argument')
                certified[m['output'][1]]=1
        self.counts['positive_power_calls_inductively_licensed']=len(records)
    def check_bindings(self):
        b=self.binding;params=b['parameters'];exp,at=self.expander()
        need(b['row_coordinate_count']==11 and set(b['upper'])==set(b['encoded_columns'])=={'p','q','v','a','b','c','d','S','Sp','u','vq'},'wrong short-beta coordinates')
        y=at(params['y']);M0=at(params['M0']);N=at(params['t']);x=at(params['x']);u=at(b['private_bound']);m=at(params['m'])
        need(y==add(M0,num(2),self.v('y0')),'beta scale parameterization')
        need(N==add(self.v('N0'),num(1)) and m==add(self.v('m0'),num(1)),'positive outer shifts')
        for name in b['upper']:
            upper=at(b['upper'][name]);lower=at(b['range_lower_arguments'][name])
            if name in ('S','Sp'):need(upper==y and lower==y,'state range must be S<y')
            else:need(upper==(m if name in ('p','q','v') else u) and lower==add(upper,num(1)),'coordinate range')
            need(at(b['encoded_columns'][name])==add(self.v('CRT.column.'+name),num(1)),'positive encoded column')
        D=add(num(1),mul(add(N,num(1)),y))
        need(exp(self.named['endpoint.initial'])==sub(x,add(M0,num(2),mul(add(y,num(1)),self.v('endpoint.u0')))),'initial endpoint')
        need(exp(self.named['endpoint.final'])==sub(x,add(num(1),mul(D,self.v('endpoint.ut')))),'final endpoint')
        if b.get('height_certificate',{}).get('kind')=='syntactic_radius' or 'radius_majorant' in b:
            self.check_radius();self.counts['exact_short_beta_bindings']=True;return
        if b.get('negative_moduli',False):
            self.counts['exact_short_beta_bindings']=True;return
        # Do not expand the enormous source pair: inspect its actual sum and
        # an all-addition path from E to x*x. This is exactly what H>=N uses.
        cut=[b['upper_E'],b['upper_F']];ee,aa=self.expander(cut)
        need(aa(b['H'])==add(aa(b['upper_E']),aa(b['upper_F'])),'majorant E+F')
        xidx=params['x'][1]
        def sum_path(i):
            if i not in self.gates:return None
            rhs=self.gate_rhs(i)
            if rhs=={(xidx,xidx):1}:return [i]
            if all(len(mon)<=1 for mon in rhs):
                for mon,c in rhs.items():
                    if mon and c>0:
                        p=sum_path(mon[0])
                        if p:return [i]+p
            return None
        path=sum_path(b['upper_E'][1]);need(path,'missing x-square majorant path')
        self.counts['majorant_x_square_addition_path']=path
        self.counts['exact_short_beta_bindings']=True
    def check_radius(self):
        b=self.binding;c=b.get('height_certificate',b.get('radius_majorant'));params=b['parameters'];R=c.get('radius',c.get('radius_atom'));D=c['exponent']
        cuts=list(params.values())+[b['private_bound']];ex,at=self.expander(cuts)
        expect=add(num(4),*(at(params[n]) for n in ['t','x','y','m','M0']),at(b['private_bound']))
        need(at(R)==expect,'radius not the stated sum')
        # Certify fixed exponent directly in multiplication-only gate DAG.
        cache={}
        def exponent(a):
            if a==R:return 1
            if a[0]=='c':need(a[1]==1,'fixed-power nonunit constant');return 0
            i=a[1]
            if i in cache:return cache[i]
            need(i in self.gates and self.gate_ops[i]=='mul','fixed power has nonmultiplication node')
            p=self.gate_rhs(i);need(len(p)==1,'fixed power is not a monomial')
            mon,coef=next(iter(p.items()));need(coef==1 and len(mon)==2,'fixed-power coefficient')
            cache[i]=sum(exponent(['v',j]) for j in mon);return cache[i]
        need(exponent(b['H'])==D and D>=1,'fixed radius exponent mismatch')
        # Positive variant: recompute the source exponent from the actual
        # encoded source DAG, stopping precisely at its row inputs.
        if not b.get('negative_moduli',False):
            leaves={a[1] for a in list(params.values())+list(b['encoded_columns'].values())+[b['encoded_index']] if a[0]=='v'}
            memo={}
            def const_degree(n):
                need(0<=n<=4,'source constant exceeds radius floor')
                return 0 if n<=1 else 1
            def h(i):
                if i in leaves:return 1
                if i in memo:return memo[i]
                need(i in self.gates,'source has undeclared input')
                p=self.gate_rhs(i);op=self.gate_ops[i]
                if op=='mul':
                    need(len(p)==1,'multiplication is not a monomial')
                    mon,coef=next(iter(p.items()));memo[i]=const_degree(coef)+sum(h(j) for j in mon)
                else:
                    need(op=='add' and all(len(mon)<=1 for mon in p),'unexpected source operation')
                    values=[]
                    for mon,coef in p.items():
                        if not mon:values.append(const_degree(coef))
                        else:
                            need(coef in (1,2),'addition coefficient not one/two')
                            values.extend([h(mon[0])]*coef)
                    need(len(values)==2,'addition is not binary');memo[i]=max(values)+1
                return memo[i]
            de,df=h(b['encoded_E'][1]),h(b['encoded_F'][1])
            if 'radius_majorant' in b:
                needed=max(1,de,df)
                need(c['E_exponent']==de and c['F_exponent']==df and c['minimum_sufficient_exponent']==needed,'recorded source exponent mismatch')
                need(D==1 << (needed-1).bit_length(),'dyadic radius bound insufficient/noncanonical')
                self.counts['radius_bounds']='E<=H and F<=H separately; not a claim E+F<=H'
            else:
                inferred=max(de,df)+1
                need(inferred==D,'literal source radius degree mismatch')
            self.counts['literal_radius_source_nodes']=len(memo)
        self.counts['fixed_radius_exponent']=D;self.counts['fixed_radius_multiplication_gates']=len(cache)
        self.counts['radius_lower_bound']='R = 4+N+x+y+m+M0+U; all row inputs and lower range arguments <= R'
    def run(self):
        self.check_gates();self.check_restoration();self.check_expansion();self.check_powers();self.check_congruences();self.check_compositions();self.check_bindings();self.check_positivity()
        self.counts['status']='PASS';self.counts['scope']='exact finite JSON algebra and named graph checks; no upstream code execution, no kernel certification'
        self.counts['sha256']={n:sha(self.path/n) for n in ['circuit.json','equation.json','expanded_polynomial.json']}
        return self.counts

def main():
    p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    result=Audit(a.candidate).run();s=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')
if __name__=='__main__':main()
