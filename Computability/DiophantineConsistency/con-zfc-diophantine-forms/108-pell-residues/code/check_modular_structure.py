#!/usr/bin/env python3
"""Independent binding of cofinal modular arithmetic to the literal source655.

Imports only the inherited independent polynomial expander, never a builder.
Checks raw total natural gates, requested indexed pairs, exact modular rows,
range and growth syntax, and the full raw-to-export affine transformation.
"""
from pathlib import Path
from copy import deepcopy
import argparse,json,hashlib
from audit_new import Audit,add,scale,mul,var,constant,atom,require


def loadpoly(terms):
    p={}
    for c,m in terms:p[tuple(m)]=p.get(tuple(m),0)+c
    return {m:c for m,c in p.items() if c}

def dump(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]

def subpoly(p,subs):
    out={}
    for m,c in p.items():
        term=constant(c)
        for i in m:term=mul(term,subs[i])
        out=add(out,term)
    return out


def affine_export_check(raw,exported):
    """Independently eliminate total affine definitions, then retain live rows."""
    defs={};sq={r['output'][1]:r for r in raw['square_difference_gates']}
    gates={int(v):rid for v,rid in raw['gates'].items()}
    require(gates=={r['gate']:i for i,r in enumerate(raw['rows']) if r['gate'] is not None},'gate index ledger')
    for v,rid in sorted(gates.items()):
        row=raw['rows'][rid];p=loadpoly(row['terms'])
        require(p.get((v,))==1 and all(v not in mon for mon in p if mon!=(v,)),'monic gate')
        rhs={mon:-c for mon,c in p.items() if mon!=(v,)}
        require(all(j<v for mon in rhs for j in mon),'triangular gate')
        if v in sq:
            r=sq[v];left,right=atom(r['left']),atom(r['right'])
            ap=lambda a:constant(a[1]) if a[0]=='c' else var(a[1])
            d=add(ap(left),scale(ap(right),-1))
            require(rhs==mul(d,d),'square-difference gate')
        else:
            require(all(c>=0 for c in rhs.values()),'negative arithmetic gate')
            require(row['label'] in ('addition','multiplication'),'unsupported total gate')
        defs[v]=rhs
    subs={};erows=set()
    for v in range(len(raw['variables'])):
        if v in defs and all(len(m)<=1 for m in defs[v]):
            expanded=subpoly(defs[v],subs)
            require(all(c>=0 and len(m)<=1 for m,c in expanded.items()),'affine sign')
            if len(expanded)<=4:
                subs[v]=expanded;erows.add(gates[v]);continue
        subs[v]=var(v)
    rows=[]
    for rid,r in enumerate(raw['rows']):
        if rid in erows:continue
        p=subpoly(loadpoly(r['terms']),subs)
        require(all(len(m)<=2 for m in p),'affine degree')
        if p:rows.append({'label':r['label'],'terms':dump(p),'gate':r['gate']})
    gate_rows={r['gate']:i for i,r in enumerate(rows) if r['gate'] is not None}
    live_rows={i for i,r in enumerate(rows) if r['gate'] is None}
    live_vars={v for i in live_rows for c,mon in rows[i]['terms'] for v in mon}
    while True:
        new_rows={gate_rows[v] for v in live_vars if v in gate_rows}-live_rows
        if not new_rows:break
        live_rows|=new_rows
        live_vars|={v for i in new_rows for c,mon in rows[i]['terms'] for v in mon}
    retained=sorted(live_vars);remap={v:i for i,v in enumerate(retained)}
    result=[{'label':r['label'],'terms':[[c,[remap[v] for v in mon]] for c,mon in r['terms']]}
            for i,r in enumerate(rows) if i in live_rows]
    require(result==exported['residuals'],'literal raw-to-export residual binding')
    require([raw['variables'][v] for v in retained]==exported['variables'],'literal exported coordinate binding')
    require(len(erows)==exported['metrics']['affine_gate_variables_eliminated'],'affine count')
    return {'raw_variables':len(raw['variables']),'raw_rows':len(raw['rows']),'total_natural_gates':len(defs),
            'affine_eliminations':len(erows),'exported_variables':len(retained),'exported_rows':len(result),
            'exact_raw_to_export_binding':True}


class ModularAudit(Audit):
    def __init__(self,data):
        super().__init__(data)
        self.names={v['name']:i for i,v in enumerate(data['variables'])}
    def named(self,name):
        require(name in self.names,'missing named role '+name)
        return ('v',self.names[name])
    def leaves(self,*ats):return {atom(a)[1]:var(atom(a)[1]) for a in ats if atom(a)[0]=='v'}
    def p(self,a):return constant(a[1]) if a[0]=='c' else var(a[1])
    def checkrow(self,label,expected,leaves):
        require(label in self.bylabel,'missing arithmetic row '+label)
        require(self.row_poly(label,leaves)==expected,'row identity '+label)
    def check_definition(self,a,expected,leaves,label):
        require(self.expand(a,leaves)==expected,'definition '+label)
    def normpoly(self,a,x,y):
        return add(add(mul(x,x),mul(y,y)),scale(add(constant(1),mul(mul(a,a),mul(y,y))),-1))
    def run(self):
        d=self.d;rd=d['radix'];p=self.p
        W,A,Z=map(atom,d['scale']);L=atom(d['lower_A']);sigma=self.named('shared.A_slack');z0=self.named('shared.Zminus1')
        self.check_definition(A,add(p(L),p(sigma)),self.leaves(L,sigma),'A=L+sigma')
        self.check_definition(Z,add(p(z0),constant(1)),self.leaves(z0),'Z=z+1')
        self.checkrow('shared.last_norm_lower',self.normpoly(add(p(W),constant(1)),p(L),mul(p(W),p(Z))),self.leaves(W,L,Z))
        exact_atoms={atom(x) for r in d['powers'] for x in (r['base'],r['exponent'],r['output'])}
        frame_leaves={i:var(i) for i in range(len(d['variables'])) if i not in self.gates or any(len(mon)>1 for c,mon in self.gates[i]['terms'])}
        expected=add(p(W),constant(-2))
        for a in exact_atoms:expected=add(expected,scale(self.expand(a,frame_leaves),-1))
        self.checkrow('shared.frame_definition',expected,frame_leaves)
        require(all(self.positive(r['exponent']) for r in d['powers']),'positive exact exponents')
        # Pair partition and the three exact shift identities.
        seeds={atom(r['exponent']):tuple(map(atom,r['pair'])) for r in d['seeds']}
        indices={atom(r['exponent']):tuple(map(atom,r['pair'])) for r in d['indices']}
        derivs={atom(r['target']):r for r in d['derivations']}
        requested={atom(r['exponent']) for r in d['powers']}|{atom(r['n']) for r in rd['modular_requests']}
        require(set(seeds).isdisjoint(derivs) and set(seeds)|set(derivs)==set(indices)==requested,'complete index partition')
        require(len(seeds)==15 and len(derivs)==3,'index census')
        D=atom(d['discriminant'])
        self.checkrow('index_addition.D_definition',add(add(mul(p(A),p(A)),scale(p(D),-1)),constant(-1)),self.leaves(A,D))
        for k,r in derivs.items():
            require(r['kind']=='shift' and r['shift'] in(1,2),'shift certificate')
            src=atom(r['source']);shift=r['shift'];require(src in requested and src[1]<k[1],'acyclic exponent')
            require(self.expand(k,self.leaves(src))==add(p(src),constant(shift)),'shift exponent binding')
            x,y=indices[src];xp,yp=tuple(map(atom,r['pair']))
            require(indices[k]==(xp,yp),'derived pair coordinates')
            dd=add(mul(p(A),p(A)),constant(-1))
            u,v=(p(A),constant(1)) if shift==1 else(add(scale(dd,2),constant(1)),scale(p(A),2))
            leaves=self.leaves(A,x,y)
            require(self.expand(xp,leaves,True)==add(mul(p(x),u),mul(dd,mul(p(y),v))),'X addition identity')
            require(self.expand(yp,leaves,True)==add(mul(p(x),v),mul(p(y),u)),'Y addition identity')
        U,V,Baux=map(atom,d['auxiliary'])
        for k,(X,Y) in seeds.items():
            tag=d['variables'][X[1]]['name'].removesuffix('.X')
            S,R,e,sq,rq=[self.named(tag+'.'+s) for s in ('S','R','YminusK','Squotient','Rquotient')]
            leaves=self.leaves(A,Baux,U,k,X,Y,S,R,e,sq,rq)
            self.checkrow(tag+'.index_at_most_Y',add(p(Y),scale(add(p(k),p(e)),-1)),leaves)
            self.checkrow(tag+'.norm1',self.normpoly(p(A),p(X),p(Y)),leaves)
            self.checkrow(tag+'.norm3',self.normpoly(p(Baux),p(S),p(R)),leaves)
            self.checkrow(tag+'.S_mod_U',add(p(S),scale(add(p(X),mul(p(U),p(sq))),-1)),leaves)
            self.checkrow(tag+'.R_mod_4Y',add(p(R),scale(add(p(k),scale(mul(p(Y),p(rq)),4)),-1)),leaves)
        vm=self.named('shared_index.Vquotient_minus1');prod=constant(1)
        for X,Y in seeds.values():prod=mul(prod,mul(p(Y),p(Y)))
        self.checkrow('shared_index.V_positive_product',add(p(V),scale(mul(prod,add(p(vm),constant(1))),-1)),self.leaves(V,vm,*[Y for X,Y in seeds.values()]))
        self.checkrow('shared_index.norm',self.normpoly(p(A),p(U),p(V)),self.leaves(A,U,V))
        auxq=self.named('shared_index.q4minus1');auxb=self.named('shared_index.Bquotient')
        self.check_definition(Baux,add(constant(1),scale(mul(p(V),add(p(auxq),constant(1))),4)),self.leaves(V,auxq),'shared comparison base')
        self.checkrow('shared_index.B_mod_U',add(p(Baux),scale(add(p(A),mul(p(U),p(auxb))),-1)),self.leaves(Baux,A,U,auxb))
        # Bind all retained exact positive-power congruences and their base moduli.
        base_moduli={}
        base_atoms=[atom(r['base']) for r in d['powers']]
        for request in d['powers']:
            n,k,m=map(atom,[request['base'],request['exponent'],request['output']])
            require(k in indices,'exact power index exists')
            if n not in base_moduli:
                matches=[]
                for name,i in self.names.items():
                    if name.startswith('base') and name.endswith('.T'):
                        T=('v',i);label=name.removesuffix('.T')+'.T_definition'
                        expected=add(scale(mul(p(A),p(n)),2),scale(add(add(p(T),mul(p(n),p(n))),constant(1)),-1))
                        if self.row_poly(label,self.leaves(A,T,*base_atoms))==expected:matches.append(T)
                require(len(matches)==1,'unique exact-power modulus')
                base_moduli[n]=matches[0]
            T=base_moduli[n];X,Y=indices[k]
            tag=d['variables'][m[1]]['name'].removesuffix('.output')
            h=self.named(tag+'.quotient')
            expected=add(add(p(X),mul(p(n),p(Y))),scale(add(add(mul(p(A),p(Y)),p(m)),mul(p(T),p(h))),-1))
            self.checkrow(tag+'.power_congruence',expected,self.leaves(X,Y,n,A,m,T,h))
        require(len(d['powers'])==12,'exact-power census')
        # Recycled radix and common modulus.
        q,B,b,M,h0=map(atom,[rd['radix'],rd['radix_multiple'],rd['root_base'],rd['common_root_modulus'],rd['root_quotient']])
        H=atom(rd['top_exponent']);FH=rd['factorial_radix'];VH=atom(FH['numerator']);rho=atom(FH['rho'])
        self.check_definition(q,mul(p(B),add(p(VH),constant(1))),self.leaves(B,VH),'recycled radix')
        self.check_definition(b,add(p(q),constant(1)),self.leaves(q),'root base')
        powers={(atom(r['base']),atom(r['exponent'])):atom(r['output']) for r in d['powers']}
        require((q,H) in powers,'q^H exists as exact power');topden=powers[q,H]
        self.check_definition(M,mul(p(q),p(topden)),self.leaves(q,topden),'common modulus')
        self.checkrow('modular.common_root',add(add(scale(mul(p(A),p(b)),2),scale(mul(p(b),p(b)),-1)),add(constant(-1),scale(mul(p(M),p(h0)),-1))),self.leaves(A,b,M,h0))
        # Check H dominates every lower index by literal monotone source syntax.
        sqcount=0;Rbase=H
        while Rbase[0]=='v' and Rbase[1] in self.gates:
            row=self.gates[Rbase[1]];rhs=[(-c,mon) for c,mon in row['terms'] if mon!=[Rbase[1]]]
            if len(rhs)!=1 or rhs[0][0]!=1 or len(rhs[0][1])!=2 or rhs[0][1][0]!=rhs[0][1][1]:break
            Rbase=('v',rhs[0][1][0]);sqcount+=1
        require(sqcount==23,'literal H squaring chain')
        t0,x,y,m0=[self.named(s) for s in ('t0','x','y','M0')];outer=self.leaves(t0,x,y,m0)
        rb=constant(3)
        for a in (t0,x,y,m0):rb=add(rb,p(a))
        self.check_definition(Rbase,rb,outer,'R=3+t0+x+y+M0')
        allowed=[add(p(t0),constant(1)),add(p(t0),constant(2)),add(p(x),constant(1)),add(p(y),constant(1))]
        for request in rd['modular_requests']:
            k=atom(request['k'])
            require(k==H or self.expand(k,outer) in allowed,'lower index dominated by H')
        # Bind all three exact requests and eight divisibility requests.
        exact={(atom(r['n']),atom(r['k'])):atom(r['output']) for r in d['binomials']}
        ranges={(atom(n),atom(k),label):atom(bb) for n,k,bb,label in d['ranges']}
        require(len(exact)==3 and len(ranges)==8 and len(rd['modular_requests'])==11,'request census')
        seen_exact=set();seen_ranges=set()
        for req in rd['modular_requests']:
            n,k,den=map(atom,[req['n'],req['k'],req['den']]);label=req['label']
            require(self.positive(n) and self.positive(k),'positive modular indices')
            require(powers.get((q,k))==den,'exact denominator binding')
            X,Y=map(atom,req['pair']);require(indices[n]==(X,Y),'requested Pell pair binding')
            mod,h,r,s=map(atom,[req['modulus'],req['quotient'],req['remainder'],req['remainder_slack']])
            residue=p(r);leaves=self.leaves(X,Y,A,b,r,den,mod,h,s)
            if req['kind']=='exact':
                c=atom(req['output']);require(exact.get((n,k))==c,'exact request identity');seen_exact.add((n,k))
                o=self.named(label+'.modular_oslack');leaves.update(self.leaves(c,o,q))
                self.checkrow(label+'.digit_bound',add(p(q),scale(add(add(p(c),p(o)),constant(1)),-1)),leaves)
                residue=add(residue,mul(p(den),p(c)))
                self.check_definition(mod,mul(p(den),p(q)),self.leaves(den,q),'exact digit modulus')
            else:
                require(req['kind']=='divisible' and ranges.get((n,k,label))==B,'range request identity');seen_ranges.add((n,k,label))
                self.check_definition(mod,mul(p(den),p(B)),self.leaves(den,B),'range modulus')
            expected=add(add(p(X),mul(p(b),p(Y))),scale(add(add(mul(p(A),p(Y)),residue),mul(p(mod),p(h))),-1))
            self.checkrow(label+'.modular_digit',expected,leaves)
            self.checkrow(label+'.remainder_bound',add(p(den),scale(add(add(p(r),p(s)),constant(1)),-1)),leaves)
        require(seen_exact==set(exact) and seen_ranges==set(ranges),'complete request coverage')
        # Bind the same factorial numerator and aggregate guard used by the inherited low-digit proof.
        po={atom(r['output']):r for r in d['powers']};require(rho in po and VH in po,'factorial power roles')
        for a in (po[rho]['base'],po[rho]['exponent']):
            require(self.expand(a,self.leaves(H))==add(p(H),constant(2)),'rho factorial binding')
        require(atom(po[VH]['exponent'])==H,'factorial numerator exponent')
        require(self.expand(po[VH]['base'],self.leaves(rho))==add(p(rho),constant(1)),'factorial numerator base')
        g=atom(rd['aggregate_slack']);agg=add(scale(p(B),8),scale(p(g),-1));leaves=self.leaves(B,g)
        for n,k,bb,label in d['ranges']:
            n=atom(n);leaves.update(self.leaves(n));agg=add(agg,scale(p(n),-1))
        self.checkrow('crt.aggregate_representative_bound',agg,leaves)
        return {'verified':True,'exact_power_requests':len(d['powers']),'modular_exact_digits':3,'modular_divisibility_tests':8,
                'seed_indices':len(seeds),'derived_indices':len(derivs),'positive_request_exponents':True,
                'common_root_and_all_modular_rows_bound':True,'cofinal_growth_rows_bound':True,
                'H_dominates_every_lower_index_by_literal_syntax':True,'inherited_radix_and_aggregate_bound':True}


def verify(raw,source):
    result=ModularAudit(raw).run();result.update(affine_export_check(raw,source));return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('raw',type=Path);p.add_argument('source',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();raw=json.loads(a.raw.read_text());source=json.loads(a.source.read_text());result=verify(raw,source)
    mutations=[]
    bad=deepcopy(raw);next(r for r in bad['rows'] if r['label']=='modular.common_root')['terms'][0][0]+=1;mutations.append(('root_row_coefficient',bad,source))
    bad=deepcopy(raw);bad['radix']['modular_requests'][0]['pair']=bad['radix']['modular_requests'][1]['pair'];mutations.append(('wrong_pell_pair',bad,source))
    bad=deepcopy(source);bad['residuals'][0]['terms'][0][0]+=1;mutations.append(('exported_coefficient',raw,bad))
    rejected=[]
    for label,r,s in mutations:
        try:verify(r,s)
        except (ValueError,KeyError):rejected.append(label)
        else:raise ValueError('negative control accepted: '+label)
    result['negative_controls_rejected']=rejected;result['status']='PASS'
    result['raw_sha256']=hashlib.sha256(a.raw.read_bytes()).hexdigest();result['source_sha256']=hashlib.sha256(a.source.read_bytes()).hexdigest()
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
