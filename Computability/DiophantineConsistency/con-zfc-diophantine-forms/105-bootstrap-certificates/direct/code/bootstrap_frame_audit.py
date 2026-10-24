"""Inherited exact graph audit, reviewed census 23 powers/12 binomials; positivity lower bounds saturate at 2."""
from collections import defaultdict
from verify_synchronized import need

def bootstrap_frame_audit(b,cert):
    gates={out: (op,a,c) for (op,a,c),out in b.cache.items()}
    lower={('v',i):0 for i in range(len(b.variables))}
    def lb(atom):return atom[1] if atom[0]=='c' else lower[atom]
    for (op,a,c),out in b.cache.items():
        lower[out]=min(2,lb(a)+lb(c) if op=='add' else lb(a)*lb(c))
    need(len(b.powers)==23,'changed power count; review new source')
    need(all(lb(k)>=1 for n,k in b.powers),'power exponent positivity not syntactic')
    need(len(b.binomials)==12,'changed binomial count')
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

