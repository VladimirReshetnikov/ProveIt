#!/usr/bin/env python3
"""Exact independent source/circuit/degree checks. Standard library; no builder imports.
Finite certificates are not a proof-assistant verification of the imported
unbounded machine/compiler and Lucas theorems. See section.tex.
"""
from pathlib import Path
from itertools import combinations_with_replacement, product
from collections import Counter, defaultdict
from math import comb, factorial
from functools import reduce
import gzip, hashlib, json, random
R=Path(__file__).resolve().parent
KAPPA=2134940
VARIABLES=['f','g','h','k','l','w','x','y','z','m']

def require(ok,msg):
    if not ok: raise RuntimeError(msg)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def ports_and_binding():
    binding=json.loads((R/'data/coefficients_binding.json').read_text())
    values=[]
    for row in binding['files']:
        path=R/'data'/(row['name']+'.bin.gz');raw=gzip.decompress(path.read_bytes())
        require(sha(path)==row['gzip_sha256'],'compressed port hash '+row['name'])
        require(hashlib.sha256(raw).hexdigest()==row['sha256'],'raw port hash '+row['name'])
        value=int.from_bytes(raw,'little')
        require(len(raw)==row['bytes'] and value.bit_length()==row['bit_length'],'port size')
        values.append(value)
    require([a['name'] for a in binding['files']]==['beta','K','MC','MF_source'],'port order')
    return values

def derive_source(records):
    src=json.loads((R/'data/parent_quartic31.json').read_text());n=31
    require(src['variables']==records['variables'] and src['constants']==records['ports'],'source variable and port order')
    require(sha(R/'data/parent_quartic31.json')==records['source_sha256'],'source hash')
    blocks={}
    for number,eq in enumerate(src['equations'],1):
        expanded=defaultdict(int)
        for term in eq['terms']:
            ex=term['powers'];supp=[i for i in range(n) if ex[i]]
            for ks in product(*(range(ex[i]+1) for i in supp)):
                alpha=[0]*n;c=term['coefficient']
                for i,k in zip(supp,ks):alpha[i]=k;c*=comb(ex[i],k)
                expanded[tuple(alpha)+tuple(ex[n:])]+=c
        grouped=defaultdict(dict)
        for exp,c in sorted(expanded.items()):
            if not c:continue
            alpha=exp[:n];require(sum(alpha)<=2,'nonquadratic source')
            factor=factorial(2-sum(alpha))*reduce(lambda a,b:a*b,(factorial(e) for e in alpha),1)
            grouped[alpha][exp[n:]]=c*factor
        blocks[number]=(eq['equation'],grouped)
    seen=set()
    for block in records['blocks']:
        j=block['source_equation'];require(j not in seen,'duplicate source equation');seen.add(j)
        eq,expected=blocks[j];require(eq==block['equation'],'source equation text')
        actual={tuple(row['alpha']):{tuple(x['powers']):x['coefficient'] for x in row['recipe']} for row in block['records']}
        require(actual==dict(expected),'weighted source reconstruction '+str(j))
        for row in block['records']:
            ref=row['coefficient'];recipe=row['recipe']
            if 'literal' in ref:
                require(recipe==[{'powers':[0]*len(src['constants']),'coefficient':ref['literal']}],'literal recipe')
            else:require(records['recipes'][ref['fixed']]==recipe,'fixed recipe binding')
    require(seen==set(range(1,23)),'all source equations')
    return {'status':'PASS','shift':'each positive parent coordinate = nonnegative coordinate + 1','equations':22,'weighted_terms':sum(len(b['records']) for b in records['blocks'])}

def source_audit(records,params,values):
    w=params['weights'];targets=params['targets']
    require(len(w)==32 and w[0]==0 and min(w[1:])>0 and len(set(w))==32,'positions')
    require([b['source_equation'] for b in records['blocks']]==params['order'],'block order')
    require(len(targets)==22 and len(set(targets))==22,'targets')
    pairs=list(combinations_with_replacement(range(32),2));ps=[w[a]+w[b] for a,b in pairs]
    target_index={q:k for k,q in enumerate(targets)};interactions=0;hits=0;seen={};bounds=[]
    bitlengths=[v.bit_length() for v in values]
    for j,(q,block) in enumerate(zip(targets,records['blocks'])):
        for row in block['records']:
            alpha=row['alpha'];pair=tuple(i+1 for i,e in enumerate(alpha) for _ in range(e))
            pair=(0,)*(2-len(pair))+pair;de=q-sum(a*x for a,x in zip(alpha,w[1:]))
            require(de>=0,'negative reversed exponent');require(de not in seen,'D support collision');seen[de]=(j,row)
            bound=sum(abs(a['coefficient'])*(1<<sum(e*l for e,l in zip(a['powers'],bitlengths))) for a in row['recipe'])
            bounds.append(bound)
            for actual,sp in zip(pairs,ps):
                landed=target_index.get(de+sp)
                require((landed is None) if actual!=pair else landed==j,'target isolation')
                hits+=landed is not None;interactions+=1
    top=max(seen);j,row=seen[top]
    require(top==max(targets) and row['coefficient']=={'literal':2} and sum(row['alpha'])==0,'positive leading coefficient')
    A=max(bounds);beta=1<<KAPPA
    require(beta>max(64*A,4*32**2*A),'coefficient majorant bound')
    require(max(w)==183 and max(targets)==5190,'canonical layout')
    return {'status':'PASS','interactions':interactions,'target_hits':hits,'D_records':len(seen),'distinct_pair_sums':len(set(ps)),
            'all_pairs':len(pairs),'largest_reversed_exponent':top,'largest_weight':max(w),
            'largest_coefficient_majorant_bitlength':A.bit_length(),'beta_exponent':KAPPA,
            'beta_over_majorant_integer_lower_bound':beta//A,'port_bitlengths':bitlengths}

class Poly:
    """Sparse exact integer polynomial, used only on finite local identities."""
    def __init__(self,terms=0):
        self.t=({():terms} if terms else {}) if isinstance(terms,int) else {m:c for m,c in terms.items() if c}
    @staticmethod
    def var(s):return Poly({((s,1),):1})
    def __add__(self,other):
        other=poly(other);d=self.t.copy()
        for m,c in other.t.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o):return self+-poly(o)
    def __rsub__(self,o):return poly(o)+-self
    def __mul__(self,other):
        other=poly(other);d=defaultdict(int)
        for a,c in self.t.items():
            for b,e in other.t.items():
                m=dict(a)
                for s,k in b:m[s]=m.get(s,0)+k
                d[tuple(sorted(m.items()))]+=c*e
        return Poly(dict(d))
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'polynomial power')
        out=Poly(1);x=self
        while n:
            if n&1:out=out*x
            n//=2
            if n:x=x*x
        return out
    def names(self):return {s for m in self.t for s,e in m}
    def __eq__(self,o):return self.t==poly(o).t

def poly(x):return x if isinstance(x,Poly) else Poly(x)

def circuit_audit(body,records,params):
    nodes=body['nodes'];named=body['named_nodes'];counts=Counter(n['kind'] for n in nodes)
    require(body['output']==named['F10'],'canonical output')
    require(body['variables']==VARIABLES and body['domain']=='Z','domain')
    require([n['name'] for n in nodes if n['kind']=='variable']==VARIABLES,'variable leaves')
    fixed=set(records['recipes'])|{'beta_source','beta_mask'}
    for i,n in enumerate(nodes):
        k=n['kind'];require(k in {'variable','literal','fixed','add','sub','mul'},'gate kind')
        if k in {'add','sub','mul'}:require(0<=n['left']<i and 0<=n['right']<i,'topological order')
        elif k=='fixed':require(n['name'] in fixed,'bound fixed leaf')
        elif k=='literal':require(isinstance(n['value'],int),'integer literal')
    live=set();todo=[body['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i);n=nodes[i]
        if n['kind'] in {'add','sub','mul'}:todo.extend([n['left'],n['right']])
    require(live==set(range(len(nodes))),'no dead gates')
    actual_counts={k:counts[k] for k in ['add','sub','mul']};require(actual_counts==body['operation_counts'],'operation ledger')
    names=set(named)|set(VARIABLES)|fixed;P={s:Poly.var(s) for s in names};p=P.__getitem__
    w=params['weights'];q=params['targets'];t=max(w);Q=max(q);K=Q+2*t;H=2*t+K+3+22
    expected={
        'b':1+3*p('f'), 'base':p('beta_source')*p('b')**2,'top':p('base')**t,
        'ell':sum(p('base')**e for e in w[1:]),
        'N0':p('base')*p('top'),'N1':p('base')**(K+1),'N':p('N0')*p('N1'),
        'Mcode':p('N0')-1-(p('b')-1)*p('ell'),
        'target':sum(p('base')**e for e in q),
        'Tcode':p('Mcode')+(p('base')-2)*p('target')*p('N0'),
        'Jcode':2*(1+p('g'))**2*p('Dcode')+p('target'),
        'Scode':p('g')+p('Jcode')*p('N0'),
        'X':p('N')**2+(p('Scode')+p('Tcode'))*p('N')+p('N')-1-p('Scode'),
        'Y':p('beta_source')**15*p('beta_mask')*p('base')**(H-16)*p('b'),
        'Ccap':p('b')*p('top'),
        'Lsmall':p('l')*p('Y'),'U':2*p('Lsmall')*p('X'),'V':4*p('g')*p('w')*p('Y'),'Wsmall':p('b')*p('w'),
        'A':p('U')*(p('V')+1),'Bsmall':2*p('X')+1,'C':p('Bsmall')+(p('A')-2)*p('h'),
        'Pn':p('U')**2*p('V'),'K':p('X')+1+p('k')*(p('Pn')-2),
        'Ssmall':2*p('A')-5,'Tsmall':3*p('Wsmall')*p('C')-2*(p('Wsmall')**2-1),
        'R2':(p('Pn')**2-4)*p('K')**2+4,
        'Delta':8*p('Ccap')**3*p('g')*p('K')**2-p('g')**2*(32*(p('C')-p('K')*p('Lsmall'))**2*p('Ccap')**3+p('g')**2*p('K')**2),
        'O0':p('f')**2*p('l')**2*p('Delta'),'xi':p('z')*p('x'),
        'D':(p('A')**2-4)*p('C')**2+4,'E':p('C')**2*p('D')*p('xi'),
        'F':4*(p('A')**2-4)*p('E')**2+1,'Gstar':2*(p('A')+2)*(p('A')-2)**2*p('E')**2-1,
        'Omega':16*p('E'),'Hstar':p('C')+(p('Bsmall')-p('C'))*p('F')+p('Omega')*p('F')*p('y'),
        'Istar':(p('Gstar')**2-1)*p('Hstar')**2+1,
        'Sigma':p('xi')*p('Ssmall')**5,'merger_argument':p('Tsmall')+p('Ssmall')*p('y'),
        'Theta':(p('merger_argument')**3-p('merger_argument')*p('Ssmall')**2-p('Ssmall')**3)*(p('merger_argument')**2+23*p('Ssmall')**2),
        'positivity_bracket':1+(3*p('O0')-4)*p('b')**2*p('z')**2,
        'A1':p('b')*p('positivity_bracket'),'A2':p('R2'),'A3':p('D')*p('F')*p('Istar'),
        'norm_weight1':p('A1'),'norm_weight2':p('norm_weight1')*(p('Pn')**2+p('K')**2+3),
        'norm_center':p('Sigma')*p('m')-p('Theta'),
        'scaled_A1':p('Sigma')**2*p('A1'),'scaled_A2':p('Sigma')**2*p('norm_weight1')**2*p('A2'),
        'scaled_A3':p('Sigma')**2*p('norm_weight2')**2*p('A3')}
    Dcode=Poly(0)
    for target,block in zip(q,records['blocks']):
        for row in block['records']:
            ref=row['coefficient'];c=ref['literal'] if 'literal' in ref else p(ref['fixed'])
            Dcode+=c*p('base')**(target-sum(x*y for x,y in zip(w[1:],row['alpha'])))
    expected['Dcode']=Dcode
    xx=p('norm_center')**2;v=xx+p('scaled_A3')-p('scaled_A1')-p('scaled_A2');ww=v**2+4*xx*p('scaled_A3')-4*p('scaled_A1')*p('scaled_A2')
    expected['F10']=ww**2-16*v**2*xx*p('scaled_A3')
    require(set(expected)==set(named),'all named quantities covered')
    checked=0
    for name,wanted in expected.items():
        root=named[name];allowed=wanted.names();stops={named[s]:p(s) for s in allowed if s in named};memo={}
        # Aliases have identical IDs, so verify them against the same underlying node.
        def evaluate(i):
            if i in stops:return stops[i]
            if i in memo:return memo[i]
            n=nodes[i];kind=n['kind']
            if kind=='literal':out=Poly(n['value'])
            elif kind in {'fixed','variable'}:out=p(n['name'])
            else:
                a,b=evaluate(n['left']),evaluate(n['right']);out=a+b if kind=='add' else a-b if kind=='sub' else a*b
            memo[i]=out;return out
        # Alias verification is tautological only when alias names share a node;
        # its underlying defining non-alias identity is independently checked too.
        got=evaluate(root)
        require(got==wanted,'exact circuit identity '+name);checked+=1
    return {'status':'PASS','exact_local_polynomial_identities':checked,'operation_counts':actual_counts,'total_operations':sum(actual_counts.values()),'nodes':len(nodes),'fixed_leaves':counts['fixed']}

def norm_audit():
    x,a,b,c=[Poly.var(s) for s in ['x','a','b','c']];product_poly=Poly(1)
    for signs in product([-1,1],repeat=3):product_poly*=x+signs[0]*a+signs[1]*b+signs[2]*c
    v=x*x+c*c-a*a-b*b;w=v*v+4*x*x*c*c-4*a*a*b*b
    require(product_poly==w*w-16*v*v*x*x*c*c,'three-radical norm identity')
    return {'status':'PASS','signed_factors':8,'expanded_terms':len(product_poly.t)}

def fixed_values(records,values,p):
    out={name:sum(row['coefficient']*reduce(lambda a,b:a*b,(pow(v,e,p) for v,e in zip(values,row['powers'])),1) for row in recipe)%p for name,recipe in records['recipes'].items()}
    out.update(beta_source=pow(2,KAPPA,p),beta_mask=pow(2,KAPPA+1-22,p));return out

def degree_audit(body,records,values):
    certificates=[]
    for p in [101,1009,1000003]:
        require(all(p%d for d in range(2,int(p**0.5)+1)),'prime certificate')
        fv=fixed_values(records,values,p);dd=[];lc=[]
        for node in body['nodes']:
            kind=node['kind']
            if kind=='variable':degree,value=1,1
            elif kind=='literal':degree,value=0,node['value']%p
            elif kind=='fixed':degree,value=0,fv[node['name']]
            else:
                a,b=node['left'],node['right']
                if kind=='mul':degree,value=dd[a]+dd[b],lc[a]*lc[b]%p
                else:
                    degree=max(dd[a],dd[b]);value=((lc[a] if dd[a]==degree else 0)+(1 if kind=='add' else -1)*(lc[b] if dd[b]==degree else 0))%p
            dd.append(degree);lc.append(value)
        i=body['output'];require(lc[i]!=0,'degree lower bound failed')
        require(dd[i]==body['degree_upper_bound']==21111400,'degree ledger')
        require({k:dd[i] for k,i in body['named_nodes'].items()}==body['named_degrees'],'named degree ledger')
        certificates.append({'prime':p,'leading_coefficient':lc[i]})
    return {'status':'PASS','exact_degree':dd[i],'specialization':'all ten variables equal one indeterminate','certificates':certificates}

def borrow_audit():
    count=0
    for B in [8,16,32,64,128]:
        for h in range(-B//4+1,B//4):
            for incoming in [-1,0]:
                for selected in [0,1]:
                    v=2*h+selected+incoming
                    require(v//B in [-1,0],'borrow invariant')
                    if selected:
                        require(((v%B)&(B-2)==0)==(h==0),'marked target zero test')
                    count+=1
    require(((-1)%16)&14!=0,'missing target padding negative control')
    return {'status':'PASS','coefficient_transition_cases':count,'tested_bases':[8,16,32,64,128]}

def bitcount_audit():
    total=0
    for u in range(1,8):
        N=1<<u
        for S in range(N):
            for T in range(N-S):
                X=N*N+(S+T)*N+N-1-S;threshold=u+T.bit_count()+1
                require(X.bit_count()==threshold+(S+T).bit_count()-S.bit_count()-T.bit_count(),'bitcount identity')
                require((X.bit_count()>=threshold)==((S&T)==0),'calibrated divisibility')
                total+=1
    return {'status':'PASS','exhaustive_pairs':total,'u_range':[1,7]}

def toy_source_audit():
    rng=random.Random(4317);count=0
    # 22 linear residuals in two nonnegative variables, all vanishing iff (x,y)=(2,1).
    # Last residual 2-x has positive constant, as required for unconditional D>0.
    w=[0,1,3];t=3;qq=[6+7*j for j in range(22)];Q=max(qq);K=Q+2*t;E=t+K+2;H=E+t+1+22
    rr=[{(1,0):1,(0,0):-2} if j%2==0 else {(0,1):1,(0,0):-1} for j in range(21)]+[{(0,0):2,(1,0):-1}]
    for b in [4,16,25,49]:
        B=(1<<14)*b*b;N0=B**(t+1);N=B**E;target=sum(B**q for q in qq)
        D=sum(factorial(2-sum(a))*factorial(a[0])*factorial(a[1])*v*B**(q-a[0]-3*a[1]) for q,r in zip(qq,rr) for a,v in r.items())
        low=N0-1-(b-1)*(B+B**3);T=low+(B-2)*target*N0;cap=b*B**t
        gs=[0,1,cap-1,cap,2*cap-1]+[rng.randrange(2*cap) for _ in range(12)]
        gs += [x*B+y*B**3 for x in range(min(b,5)) for y in range(min(b,4))]
        for g in gs:
            J=2*(1+g)**2*D+target;S=g+J*N0
            require(0<S and 0<T and S+T<N,'prebinary bounds')
            X=N*N+(S+T)*N+N-1-S
            require(X%3==0 and X>3*b,'source normalization')
            if b&(b-1)==0:
                k=b.bit_length()-1;v=B.bit_length()-1;u=N.bit_length()-1
                pt=(t+1+22)*v-2*k-22
                require(T.bit_count()==pt,'literal mask popcount')
                threshold=1+u+pt
                require(threshold==1-22+H*v-2*k,'threshold polynomial exponent')
                digits=[(g//B**wi)%B for wi in w[1:]]
                iscode=g==sum(x*B**wi for x,wi in zip(digits,w[1:])) and all(x<b for x in digits)
                expected=iscode and digits==[2,1]
                require(((S&T)==0)==expected,'toy sparse borrow extraction')
                require((X.bit_count()>=threshold)==expected,'toy calibrated binomial')
            count+=1
    return {'status':'PASS','source_assignments':count,'non_power_two_square_bases':[25,49]}


def main():
    body=json.loads((R/'generated/signed10_b2.json').read_text())
    records=json.loads((R/'generated/source_records.json').read_text())
    params=json.loads((R/'parameters.json').read_text());values=ports_and_binding()
    result={'source_reconstruction':derive_source(records),'selective_source':source_audit(records,params,values),
            'circuit':circuit_audit(body,records,params),'norm_identity':norm_audit(),
            'degree':degree_audit(body,records,values),'borrow':borrow_audit(),
            'bitcount':bitcount_audit(),'toy_source':toy_source_audit(),'status':'PASS'}
    pins=R/'SOURCE_PINS.json'
    if pins.exists():
        for entry in json.loads(pins.read_text())['files']:
            require(sha(R/entry['local_path'])==entry['sha256'],'pinned source hash '+entry['local_path'])
        result['pinned_dependencies']='PASS'
    result['input_sha256']={str(p.relative_to(R)):sha(p) for p in [R/'parameters.json',R/'data/parent_quartic31.json',R/'build.py',R/'circuit.py',R/'independent_check.py',R/'generated/signed10_b2.json',R/'generated/source_records.json']}
    (R/'generated/INDEPENDENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
