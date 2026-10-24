#!/usr/bin/env python3
"""Independent scoped audit of synchronized compiler, not a semantic proof kernel."""
from __future__ import annotations
import argparse, ast, hashlib, importlib.util, json, math, sys
from collections import defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
NOTES=ROOT/'code'; UP=ROOT/'provenance/upstream'
sys.path[:0]=[str(NOTES),str(UP)]
import synchronized_builder as compiler
from synchronized_builder import DeferredBinomialMixin, construct
from shared_power import SharedPowerBuilder

def need(ok,msg):
    if not ok: raise ValueError(msg)

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def function_ast(path):
    return next(n for n in ast.parse(path.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='source_pair_calculus')

def source_change(factored=False):
    old=function_ast(UP/'direct_calculus.py'); new=function_ast(NOTES/'direct_source.py')
    found=0
    for node in ast.walk(old):
        if isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name) and node.target.id=='rows' and isinstance(node.value,ast.List) and len(node.value.elts)==4:
            node.value.elts=[node.value.elts[0],node.value.elts[2]]; found+=1
    need(found==1,'expected one old four-row beta block')
    need(ast.dump(old,include_attributes=False)==ast.dump(new,include_attributes=False),'source changed beyond deletion of two remainder rows')
    ans={'beta_rows_deleted':2,'unchanged_function_AST':True}
    if factored:
        fact=function_ast(NOTES/'direct_source_factored.py')
        def split(node):
            def assign_name(stmt,name):
                return isinstance(stmt,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in stmt.targets)
            p=next(i for i,x in enumerate(node.body) if assign_name(x,'pq'))
            q=next(i for i,x in enumerate(node.body) if assign_name(x,'carrier'))
            return node.body[:p+1],node.body[q:]
        a,b=split(new);c,d=split(fact)
        dump=lambda xs:[ast.dump(x,include_attributes=False) for x in xs]
        need(dump(a)==dump(c),'factoring changed formula constructors')
        need(dump(b)==dump(d),'factoring changed accumulator/beta rows')
        ans.update({'factored_constructor_prefix_unchanged':True,'factored_accumulator_suffix_unchanged':True,
                    'branch_zero_set_argument':'pq=0 and (one unconditional difference zero OR guarded bundle zero); proof reviewed separately'})
    return ans

def majorant(cert):
    vals={i:1 for i in range(len(cert['inputs']))}
    need(tuple(cert['inputs'])==('t','x','y','m','M0'),'majorant inputs changed')
    def w(atom):
        tag,v=atom
        if tag=='c':
            need(v>=0,'negative majorant constant')
            if v<=1:return 0
            return (v-1).bit_length()
        need(tag=='v' and v in vals,'majorant reference not defined')
        return vals[v]
    for g in cert['gates']:
        need(g['output'] not in vals,'majorant duplicate output')
        a,b=w(g['left']),w(g['right'])
        need(g['operation'] in ('add','mul'),'unknown majorant operation')
        e=max(a,b)+1 if g['operation']=='add' else a+b
        # The producer is allowed a weaker exponent for the zero constant.
        need(g['exponent']>=e,'majorant exponent underestimates')
        vals[g['output']]=g['exponent']
    need(w(cert['output'])==cert['exponent'],'wrong majorant root')
    out={'checked_gate_inequalities':len(cert['gates']),'exponent':cert['exponent']}
    if 'emitted_exponent' in cert:
        n=cert['emitted_exponent']
        need(n>=cert['exponent'] and n>0 and n&(n-1)==0,'emitted majorant is not a dominating power of two')
        need(n//2<cert['exponent'],'emitted majorant is not the least dominating power of two')
        out['emitted_exponent']=n
    return out

def exact_expansion(eq,pol):
    p=defaultdict(int); n=len(eq['variables'])
    used=set()
    for row in eq['residuals']:
        terms=row['terms']
        for c,m in terms:
            need(isinstance(c,int) and len(m)<=2 and m==sorted(m),'bad quadratic term')
            need(all(isinstance(i,int) and 0<=i<n for i in m),'bad variable index')
            used.update(m)
        for c,m in terms:
            for d,k in terms:p[tuple(sorted(m+k))]+=c*d
    p={m:c for m,c in p.items() if c}
    supplied={tuple(m):c for c,m in pol['terms']}
    need(p==supplied,'expanded polynomial mismatch')
    need(len(p)==len(pol['terms']),'duplicate expanded monomials')
    need(used==set(range(n)),'dead variable')
    degree=max(map(len,p));height=max(map(abs,p.values()))
    need(degree==4,'not exact quartic')
    return {'variables':n,'residuals':len(eq['residuals']),'monomials':len(p),'degree':degree,'coefficient_height':height}

def frame_audit(b,cert):
    gates={out: (op,a,c) for (op,a,c),out in b.cache.items()}
    lower={('v',i):0 for i in range(len(b.variables))}
    def lb(atom):return atom[1] if atom[0]=='c' else lower[atom]
    for (op,a,c),out in b.cache.items():
        lower[out]=lb(a)+lb(c) if op=='add' else lb(a)*lb(c)
    need(len(b.powers)==24,'changed power count; review projected source')
    need(all(lb(k)>=1 for n,k in b.powers),'power exponent positivity not syntactic')
    need(len(b.binomials)==11,'changed projected binomial count')
    need(b.shared_frame_finalized,'power frame missing')
    W,A,Z=b.shared_parameters
    need(lb(Z)>=1,'zero common Pell ordinate allowed')
    fr=[r for r in b.rows if r['label']=='shared.frame_definition'];need(len(fr)==1,'not exactly one frame row')
    want={a for (n,k),m in b.powers.items() for a in (n,k,m)}
    # Decode all affine additions in the frame RHS; independent of primary sum helper.
    def affine(atom):
        if atom[0]=='c':return {():atom[1]}
        if atom not in gates:return {(atom[1],):1}
        op,left,right=gates[atom]
        if op=='add':
            ans=defaultdict(int,affine(left))
            for mon,c in affine(right).items():ans[mon]+=c
            return dict(ans)
        return {(atom[1],):1}
    # Stop at designated frame input atoms so their own definitions are not expanded.
    def term(atom):
        if atom in want:return {atom:1}
        if atom[0]=='c':return {('constant',):atom[1]}
        need(atom in gates,'unknown frame sum atom')
        op,l,r=gates[atom];need(op=='add','nonaddition in frame sum')
        ans=defaultdict(int,term(l))
        for x,c in term(r).items():ans[x]+=c
        return dict(ans)
    terms=fr[0]['terms']; positive=[m for c,m in terms if c==1 and m==[W[1]]]
    need(len(positive)==1,'wrong frame lhs')
    rhs_terms=[(c,m) for c,m in terms if m!=[W[1]]]
    total=defaultdict(int)
    for c,m in rhs_terms:
        need(len(m)<=1,'nonaffine frame equality')
        sub=term(('v',m[0])) if m else {('constant',):1}
        for x,v in sub.items():total[x]-=c*v
    expected=defaultdict(int,{a:1 for a in want})
    # Constants can be folded into one leaf by the primary builder.
    numeric=2+sum(a[1] for a in want if a[0]=='c')
    expected={a:1 for a in want if a[0]=='v'};expected[('constant',)]=numeric
    cooked=defaultdict(int)
    for a,c in total.items():
        if a[0]=='c':cooked[('constant',)]+=a[1]*c
        else:cooked[a]+=c
    need(dict(cooked)==expected,'frame does not bound precisely all requested atoms')
    # Check shared q exponent contains every distinct binomial upper input once.
    dat=b.shared_binomial_data; uppers={n for n,k in b.binomials}
    need({tuple(a) for a in dat['upper_atoms']}==uppers,'binomial upper set incomplete')
    q=tuple(dat['radix_atom']);K=tuple(dat['exponent_atom'])
    need(lb(K)>=1,'shared radix exponent may vanish')
    def upper_sum(atom):
        if atom in uppers and atom[0]=='v':return {atom:1}
        if atom[0]=='c':return {('constant',):atom[1]}
        need(atom in gates and gates[atom][0]=='add','nonaddition in common radix exponent')
        _,l,r=gates[atom];ans=defaultdict(int,upper_sum(l))
        for key,c in upper_sum(r).items():ans[key]+=c
        return dict(ans)
    actual_upper=upper_sum(K)
    expected_upper={a:1 for a in uppers if a[0]=='v'}
    csum=sum(a[1] for a in uppers if a[0]=='c')
    if csum:expected_upper[('constant',)]=csum
    actual_upper={a:c for a,c in actual_upper.items() if c}
    need(actual_upper==expected_upper,'common radix exponent omits/repeats an upper input')
    qdef=gates[q];need(qdef[0]=='add' and ('c',1) in qdef[1:],'q is not one plus power')
    qpower=qdef[2] if qdef[1]==('c',1) else qdef[1]
    need(b.powers.get((('c',2),K))==qpower,'q lacks power2 certificate')
    for (n,k),out in b.binomials.items():
        need(lb(n)>=1 and lb(k)>=1,'binomial positive args missing')
    # Independent syntactic exponent verification for fixed R^D.
    fac=[r for r in b.macro_log if r['macro']=='factorial'];H=fac[0]['n']
    # The fixed-power DAG terminates in multiplications whose only nonconstant
    # base is the R addition chain, identifiable by its exact additive leaves.
    input_atoms={name:('v',i) for i,name in enumerate(('t0','x','y','m0','M0'))}
    expected_R={():4,(0,):1,(1,):1,(2,):1,(3,):1,(4,):1}
    candidates=[a for a in gates if affine(a)==expected_R]
    need(candidates,'R atom missing')
    good=[]
    for R in candidates:
        memo={R:1,('c',1):0}
        def exp(atom):
            if atom in memo:return memo[atom]
            need(atom in gates and gates[atom][0]=='mul','nonpower node in fixed majorant')
            _,a,c=gates[atom];memo[atom]=exp(a)+exp(c);return memo[atom]
        try:
            if exp(tuple(H))==cert.get('emitted_exponent',cert['exponent']):good.append(R)
        except ValueError:pass
    need(good,'literal fixed majorant exponent differs')
    return {'positive_power_exponents':len(b.powers),'positive_binomial_inputs':len(b.binomials),
            'one_frame':True,'shared_radix':True,'index_certificates':len(b.shared_indices),
            'base_moduli':len(b.shared_bases),'fixed_power_exponent':cert.get('emitted_exponent',cert['exponent'])}

def product_index_audit(b):
    gates={out:(op,a,c) for (op,a,c),out in b.cache.items()}
    def named(name):
        found=[('v',i) for i,v in enumerate(b.variables) if v['name']==name]
        need(len(found)==1,'missing/duplicate named product variable');return found[0]
    vm=named('shared_index.Vquotient_minus1');qm=named('shared_index.q4minus1')
    def plus_one(x):
        hits=[out for out,(op,a,c) in gates.items() if op=='add' and {a,c}=={x,('c',1)}]
        need(len(hits)==1,'missing plus-one gate');return hits[0]
    vp,qp=plus_one(vm),plus_one(qm)
    U,V,B=b.common_index_parameters
    ys={Y for X,Y in b.shared_indices.values()}
    def factors(atom,stops):
        if atom in stops:return {atom:1},1
        if atom[0]=='c':return {},atom[1]
        need(atom in gates and gates[atom][0]=='mul','nonmultiplication in divisor product')
        _,l,r=gates[atom];a,c=factors(l,stops);bb,d=factors(r,stops)
        out=defaultdict(int,a)
        for k,v in bb.items():out[k]+=v
        return dict(out),c*d
    rs=[r for r in b.rows if r['label']=='shared_index.V_positive_product'];need(len(rs)==1,'global product row count')
    expected_positive=[[1,[V[1]]]]
    neg=[m for c,m in rs[0]['terms'] if c==-1]
    need(len(neg)==1 and len(neg[0])==1,'noncanonical global product row')
    need(sorted(rs[0]['terms'])==sorted(expected_positive+[[-1,neg[0]]]),'extra term in divisor product row')
    got,constant=factors(('v',neg[0][0]),ys|{vp})
    want={Y:2 for Y in ys};want[vp]=1
    need(got==want and constant==1,'global V misses a squared ordinate or quotient')
    op,l,r=gates[B];need(op=='add' and ('c',1) in (l,r),'global B is not 1 plus product')
    value=r if l==('c',1) else l
    got,constant=factors(value,{V,qp});need(got=={V:1,qp:1} and constant==4,'global B is not 1+4V(q+1)')
    need(not any(r['label'].endswith('.V_positive_multiple') for r in b.rows),'private V constraints remain')
    return {'squared_ordinate_factors':len(ys),'one_V_product_row':True,'B_mod_4V':True}

def common_index_fixtures(product=False):
    cases=[]
    for A in range(2,7):
        ks=(1,2,3)
        ps=[0,1]
        xs=[1,A]
        for k in range(2,4):
            ps.append(2*A*ps[-1]-ps[-2]);xs.append(2*A*xs[-1]-xs[-2])
        ys=[ps[k] for k in ks]
        L=4*math.prod(y*y for y in ys);M=4*math.prod(ys)
        # Find the finite-ring identity period using only residues.
        u,v=1,0;r=0;delta=A*A-1
        while True:
            u,v=(A*u+delta*v)%L,(u+A*v)%L;r+=1
            if (u,v)==(1,0):break
            need(r<500000,'fixture period budget exceeded')
        U,V=1,0
        for _ in range(r):U,V=A*U+delta*V,U+A*V
        need(U%L==1 and V%L==0 and V>0,'common period not integral')
        if product:
            need(V%math.prod(y*y for y in ys)==0,'shared V product fails')
            M=4*V
        need(math.gcd(U,M)==1,'shared CRT moduli not coprime')
        bq=((1-A)*pow(U,-1,M))%M
        if bq==0:bq=M
        B=A+U*bq
        ss=[1,B];rr=[0,1]
        for k in range(2,4):ss.append(2*B*ss[-1]-ss[-2]);rr.append(2*B*rr[-1]-rr[-2])
        for k,Y in zip(ks,ys):
            need(V%(Y*Y)==0 and V//(Y*Y)>=1,'missing positive shared V multiple')
            need((B-1)%(4*Y)==0 and (B-1)//(4*Y)>=1,'shared B modulus fails')
            need((ss[k]-xs[k])%U==0 and ss[k]>=xs[k],'shared S quotient fails')
            need((rr[k]-k)%(4*Y)==0 and rr[k]>=k,'shared R quotient fails')
            need(ss[k]*ss[k]-(B*B-1)*rr[k]*rr[k]==1,'shared third norm fails')
        cases.append({'A':A,'exponents':list(ks),'period':r})
    return cases

def arithmetic_fixtures():
    bins=0; calls=[(n,k) for n in range(1,9) for k in range(1,n+3)]
    q=2**sum({n for n,k in calls})+1
    for n,k in calls:
        num=(q+1)**n;den=q**k;quot,r=divmod(num,den);h,out=divmod(quot,q)
        need(out==math.comb(n,k) if k<=n else out==0,'shared radix digit wrong')
        need(0<=r<den and 0<=out<q,'invalid remainder');bins+=1
    identities=0
    for A in range(2,8):
        psi=[0,1]
        for k in range(2,13):psi.append(2*A*psi[-1]-psi[-2])
        for n in range(1,8):
            T=2*A*n-n*n-1
            for k in range(1,13):
                chi=A*psi[k]-psi[k-1]
                quotient=sum(n**j*psi[k-1-j] for j in range(k-1))
                need(chi-(A-n)*psi[k]-n**k==T*quotient,'positive quotient identity wrong')
                need(quotient>=0,'negative oriented quotient');identities+=1
    return {'binomial_digit_fixtures':bins,'oriented_quotient_identity_fixtures':identities,
            'scope':'supplementary finite regression checks; universal proofs are separate'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--equation-dir',type=Path,default=ROOT/'equations/source895');p.add_argument('--output',type=Path);p.add_argument('--shared-index',action='store_true');p.add_argument('--factored-source',action='store_true');p.add_argument('--product-index',action='store_true');a=p.parse_args()
    source=json.loads((UP/'wire_eliminated_source.json').read_text())
    if a.factored_source:
        from direct_source_factored import source_pair_calculus
        compiler.source_pair_calculus=source_pair_calculus
    if a.product_index:
        from shared_product_power import SharedProductPowerBuilder
        power_class=SharedProductPowerBuilder
    elif a.shared_index:
        from shared_index_power import SharedIndexPowerBuilder
        power_class=SharedIndexPowerBuilder
    else:power_class=SharedPowerBuilder
    class Sync(DeferredBinomialMixin,power_class):pass
    b,cert=construct(Sync,source)
    eq=json.loads((a.equation_dir/'equation.json').read_text());pol=json.loads((a.equation_dir/'expanded_polynomial.json').read_text())
    delivered=json.loads((a.equation_dir/'majorant_certificate.json').read_text());need(json.loads(json.dumps(cert))==delivered,'delivered majorant not current source')
    result={'status':'PASS','scope':'source delta, majorant induction, frame closure, syntactic positivity, literal expansion, regression fixtures',
        'source_change':source_change(a.factored_source),'majorant':majorant(cert),'frame':frame_audit(b,cert),
        'literal':exact_expansion(eq,pol),'fixtures':arithmetic_fixtures(),
        'pins':{str(p.relative_to(ROOT)):digest(p) for p in [NOTES/'synchronized_builder.py',NOTES/'direct_source.py',NOTES/'shared_power.py',UP/'wire_eliminated_source.json']}}
    fresh,fp,fm=b.export(digest(UP/'wire_eliminated_source.json'),'synchronized11',inline_affine=True)
    need(fresh['variables']==eq['variables'] and fresh['residuals']==eq['residuals'],'literal output differs from selected compiler class/source')
    need(fp['terms']==pol['terms'],'literal expanded output differs from selected compiler')
    result['literal_regeneration_matches']=True
    if a.shared_index or a.product_index:
        need(b.common_index_parameters is not None,'shared index triple missing')
        need(sum(r['label']=='shared_index.norm' for r in b.rows)==1,'not exactly one auxiliary index norm')
        need(not any(r['label'].endswith('.norm2') for r in b.rows),'old auxiliary index norm remains')
        result['frame']['common_auxiliary_index_triples']=1
        result['shared_index_fixtures']=common_index_fixtures(a.product_index)
        result['pins'][str((NOTES/'shared_index_power.py').relative_to(ROOT))]=digest(NOTES/'shared_index_power.py')
    if a.product_index:
        result['frame']['global_index_product']=product_index_audit(b)
        result['pins'][str((NOTES/'shared_product_power.py').relative_to(ROOT))]=digest(NOTES/'shared_product_power.py')
    if a.factored_source:
        result['pins'][str((NOTES/'direct_source_factored.py').relative_to(ROOT))]=digest(NOTES/'direct_source_factored.py')
    if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
