#!/usr/bin/env python3
"""Independent exact source, circuit, norm and degree verifier; no builder imports."""
from pathlib import Path
from itertools import combinations_with_replacement, product
from collections import Counter, defaultdict
from functools import reduce
import gzip, hashlib, json, random
from source_audit import audit as source_audit, add as sparse_add
R=Path(__file__).resolve().parent
KAPPA=2134940
VARIABLES=['f','g','h','k','l','w','x','y','z','m']
def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
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
        require(dd[i]==body['degree_upper_bound']==8469528,'degree ledger')
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


def record_audit(records,layout):
    src=json.loads((R/'data/parent_quartic31.json').read_text())
    require(sha(R/'data/parent_quartic31.json')==records['source_sha256'],'source record hash')
    require(src['variables']==records['variables'] and src['constants']==records['ports'],'record names')
    rows=[{tuple(t['powers']):t['coefficient'] for t in row['terms']} for row in src['equations']]
    rows[13]=sparse_add(rows[13],rows[1]); rows[14]=sparse_add(rows[14],rows[2])
    for block,number,target in zip(records['blocks'],layout['order'],layout['targets']):
        require(block['source_equation']==number and block['target']==target,'record row binding')
        actual={}
        for term in block['records']:
            alpha=tuple(term['alpha']); degree=sum(alpha)
            require(term['degree']==degree,'record degree')
            require(term['exponent']==target-sum(a*w for a,w in zip(alpha,layout['weights'])),'record exponent')
            factor=2 if degree<2 or 2 in alpha else 1
            for leaf in term['recipe']:
                require(leaf['coefficient']%factor==0,'record coefficient multiplier')
                actual[alpha+tuple(leaf['powers'])]=leaf['coefficient']//factor
            ref=term['coefficient']
            require(term['recipe']==([{'powers':[0]*4,'coefficient':ref['literal']}] if 'literal' in ref else records['recipes'][ref['fixed']]),'recipe binding')
        require(actual==rows[number-1],'source recipe equality')
    quadratic=[t for b in records['blocks'] for t in b['records'] if t['degree']==2]
    lead=max(quadratic,key=lambda t:t['exponent'])
    require(lead['exponent']==1929 and lead['coefficient']=={'literal':1},'positive leading quadratic kernel')
    return {'status':'PASS','records':sum(len(b['records']) for b in records['blocks']),'quadratic_leading_coefficient':1}


def circuit_audit(body,records,layout):
    nodes=body['nodes']; named=body['named_nodes']; counts=Counter(n['kind'] for n in nodes)
    require(body['variables']==VARIABLES and body['domain']=='Z','domain')
    require([n['name'] for n in nodes if n['kind']=='variable']==VARIABLES,'ten live variables')
    fixed=set(records['recipes'])|{'beta_source','beta_mask'}
    for i,node in enumerate(nodes):
        k=node['kind']; require(k in {'add','sub','mul','literal','fixed','variable'},'gate kind')
        if 'left' in node:require(0<=node['left']<i and 0<=node['right']<i,'topological order')
        elif k=='fixed':require(node['name'] in fixed,'unknown fixed leaf')
        elif k=='literal':require(type(node['value'])==int,'literal type')
    live=set();todo=[body['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i); n=nodes[i]
        if 'left' in n:todo.extend([n['left'],n['right']])
    require(live==set(range(len(nodes))),'dead gates')
    actual_counts={k:counts[k] for k in ('add','sub','mul')}
    require(actual_counts==body['operation_counts'] and sum(actual_counts.values())==body['total_operations'],'gate ledger')
    p=Poly.var; w=layout['weights']; q=layout['targets']; W=max(w); H=layout['convolution_height']; HP=2*W+H+25
    expected={
        'b':1+3*p('f'),'base':p('beta_source')*p('b')**2,
        'ell':sum(p('base')**e for e in w),'packed_positive':p('ell')+p('g'),
        'Gcode':p('D2')*p('packed_positive')**2+p('D1')*p('packed_positive')+p('D0'),
        'top':p('base')**W,'N0':p('base')*p('top'),'N1':p('base')**(H+1),'N':p('N0')*p('N1'),
        'mask':p('N0')-1-(p('b')-1)*p('ell'),'targets':sum(p('base')**e for e in q),
        'Tcode':p('mask')+(p('base')-2)*p('targets')*p('N0'),
        'Jcode':2*p('Gcode')+p('targets'),'Scode':p('g')+p('Jcode')*p('N0'),
        'X':p('N')**2+(p('Scode')+p('Tcode'))*p('N')+p('N')-1-p('Scode'),
        'Y':p('beta_source')**15*p('beta_mask')*p('base')**(HP-16)*p('b'),
        'Ccap':p('b')*p('top'),'L':p('l')*p('Y'),'U':2*p('L')*p('X'),
        'V':4*p('g')*p('w')*p('Y'),'W':p('b')*p('w'),
        'halfA':p('L')*p('X')*(p('V')+1),'A':2*p('halfA'),
        'B1':2*p('X')+1,'C':p('B1')+(p('A')-2)*p('h'),
        'Pn':p('U')**2*p('V'),'K':p('X')+1+p('k')*(p('Pn')-2),
        'S':2*p('A')-5,'T':3*p('W')*p('C')-2*(p('W')**2-1),
        'r1':(p('Pn')**2-4)*p('K')**2+4,'CKL':p('C')-p('K')*p('L'),
        'Delta':8*p('Ccap')**3*p('g')*p('K')**2-p('g')**2*(32*p('CKL')**2*p('Ccap')**3+p('g')**2*p('K')**2),
        'O':p('f')**2*p('l')**2*p('Delta'),'xi':p('z')*p('x'),
        'D':(p('A')**2-4)*p('C')**2+4,'E':p('C')**2*p('D')*p('xi'),
        'Fm1':4*(p('A')**2-4)*p('E')**2,'F':p('Fm1')+1,
        'G':(p('halfA')-1)*p('Fm1')-1,'Omega':16*p('E'),
        'H':p('C')+(p('B1')-p('C'))*p('F')+p('Omega')*p('F')*p('y'),
        'I':(p('G')**2-1)*p('H')**2+1,'Sigma':p('xi')*p('S')**5,
        't':p('T')+p('S')*p('y'),
        'Theta':(p('t')**3-p('t')*p('S')**2-p('S')**3)*(p('t')**2+23*p('S')**2),
        'r0':p('b')*(1+(3*p('O')-4)*p('b')**2*p('z')**2),'r2':p('D')*p('F')*p('I'),
        'separator':p('Pn')**2+p('K')**2+3,'center':p('Sigma')*p('m')-p('Theta'),
        'norm_common':p('Sigma')**2*p('r0')**2,'a0':p('Sigma')**2*p('r0'),
        'a1':p('norm_common')*p('r1'),'a2':p('norm_common')*p('separator')**2*p('r2'),
        'Vnorm':p('center')**2+p('a2')-p('a0')-p('a1'),
        'Wnorm':p('Vnorm')**2+4*p('center')**2*p('a2')-4*p('a0')*p('a1'),
        'F10':p('Wnorm')**2-16*p('Vnorm')**2*p('center')**2*p('a2')}
    for degree in range(3):
        expr=Poly(0)
        for block in records['blocks']:
            for row in block['records']:
                if row['degree']==degree:
                    ref=row['coefficient']; co=ref['literal'] if 'literal' in ref else p(ref['fixed'])
                    expr+=co*p('base')**row['exponent']
        expected['D'+str(degree)]=expr
    require(set(expected)==set(named),'all named nodes covered')
    for name,wanted in expected.items():
        stops={named[s]:p(s) for s in wanted.names() if s in named}; memo={}
        def evaluate(i):
            if i in stops:return stops[i]
            if i in memo:return memo[i]
            n=nodes[i]; k=n['kind']
            if k=='literal':value=Poly(n['value'])
            elif k in ('fixed','variable'):value=p(n['name'])
            else:
                a,b=evaluate(n['left']),evaluate(n['right']);value=a+b if k=='add' else a-b if k=='sub' else a*b
            memo[i]=value;return value
        require(evaluate(named[name])==wanted,'local polynomial identity '+name)
    a,e=p('halfA'),p('E')
    require((a-1)*4*((2*a)**2-4)*e**2-1==2*(2*a+2)*(2*a-2)**2*e**2-1,'factored Lucas G identity')
    return {'status':'PASS','local_identities':len(expected),'additional_factorization_identity':1,'operation_counts':actual_counts,'total_operations':sum(actual_counts.values()),'nodes':len(nodes)}


def source_integer_tests(records,layout):
    # Artificial small ports keep integers manageable; identities remain universal.
    pv=[2,3,5,7]; w=layout['weights']; W=max(w); H=layout['convolution_height']; targets=layout['targets']
    kernel=[{} for _ in range(3)]; residuals=[]
    for block in records['blocks']:
        rr=[]
        for term in block['records']:
            co=sum(a['coefficient']*reduce(lambda a,b:a*b,(x**e for x,e in zip(pv,a['powers'])),1) for a in term['recipe'])
            kernel[term['degree']][term['exponent']]=co;rr.append((term['alpha'],co))
        residuals.append(rr)
    rng=random.Random(890116); cases=0; marked=0
    for b in (4,16,25,49):
        B=(1<<20)*b*b; powers=[1]
        for _ in range(H+2):powers.append(powers[-1]*B)
        ell=sum(powers[e] for e in w);cap=b*powers[W];N0=powers[W+1];N1=powers[H+1];N=N0*N1
        D=[sum(c*powers[e] for e,c in ker.items()) for ker in kernel]
        target=sum(powers[e] for e in targets);mask=N0-1-(b-1)*ell;T=mask+(B-2)*target*N0
        assignments=[(None,g) for g in (0,1,cap-1,cap,2*cap-1)]
        for _ in range(10):
            ns=[rng.randrange(b) for _ in w];assignments.append((ns,sum(n*powers[e] for n,e in zip(ns,w))))
        for ns,g in assignments:
            u=ell+g; G=D[2]*u*u+D[1]*u+D[0];J=2*G+target;S=g+J*N0
            require(G>0 and 0<=S and 0<=T and S+T<N,'prebinary positivity/range')
            X=N*N+(S+T)*N+N-1-S;require(X%3==0 and X>3*b,'source congruence/size')
            if b in (4,16):
                logb=b.bit_length()-1;logB=B.bit_length()-1;expected_pop=(W+1+22)*logB-31*logb-22
                require(T.bit_count()==expected_pop,'actual mask population')
                threshold=1+(W+H+2)*logB+expected_pop
                require((X.bit_count()>=threshold)==((S&T)==0),'actual two-block threshold')
                if ns is not None:
                    require(g&mask==0,'low digit coding')
                    ps=[n+1 for n in ns]
                    for q,rr in zip(targets,residuals):
                        # Weighted coefficients multiply by cross-term factor 2.
                        h=sum(co*(2 if sum(alpha)==2 and 2 not in alpha else 1)*reduce(lambda a,b:a*b,(p**e for p,e in zip(ps,alpha)),1) for alpha,co in rr)
                        digit=(J//powers[q])%B
                        require((digit&(B-2)==0)==(h==0),'individual marked target');marked+=1
            cases+=1
    return {'status':'PASS','large_integer_source_cases':cases,'individual_marked_target_cases':marked,'nonbinary_square_bases':[25,49]}


def main():
    body=json.loads((R/'generated/sun10.json').read_text()); records=json.loads((R/'generated/source_records.json').read_text())
    layout=json.loads((R/'data/layout.json').read_text()); values=ports_and_binding()
    result={'status':'PASS','source':source_audit(),'source_records':record_audit(records,layout),
            'circuit':circuit_audit(body,records,layout),'degree':degree_audit(body,records,values),
            'norm':norm_audit(),'borrow':borrow_audit(),'population':bitcount_audit(),
            'source_integer_tests':source_integer_tests(records,layout)}
    for row in json.loads((R/'SOURCE_PINS.json').read_text())['files']:
        require(sha(R/row['local_path'])==row['sha256'],'source pin '+row['local_path'])
    manifest=json.loads((R/'INSTANCE.json').read_text())
    require(manifest['polynomial']=='generated/sun10.json','active polynomial binding')
    require(manifest['additional_fixed_leaves']=={'beta_source':{'base':2,'exponent':2134940},'beta_mask':{'base':2,'exponent':2134919}},'fixed power binding')
    require(body['beta_exponent']==KAPPA and body['popcount_power']==2418,'circuit coefficient calibration')
    result['pinned_source_files']=12
    result['file_hashes']={str(p.relative_to(R)):sha(p) for p in [R/'data/layout.json',R/'data/parent_quartic31.json',R/'build.py',R/'circuit.py',R/'source_audit.py',R/'independent_check.py',R/'generated/sun10.json',R/'generated/source_records.json']}
    (R/'generated/INDEPENDENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
