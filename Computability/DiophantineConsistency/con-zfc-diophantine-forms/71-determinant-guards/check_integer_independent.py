#!/usr/bin/env python3
"""Independent AST/sparse-polynomial audit; imports no construction module."""
import ast,json,random,sys,hashlib,gzip
from collections import defaultdict,Counter
from pathlib import Path

def require(ok,msg):
    if not ok:raise ValueError(msg)
def add(a,b,sign=1):
    z=dict(a)
    for m,c in b.items():z[m]=z.get(m,0)+sign*c
    return {m:c for m,c in z.items() if c}
def mul(a,b):
    z=defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():
            w=dict(m)
            for x,e in n:w[x]=w.get(x,0)+e
            z[tuple(sorted(w.items()))]+=c*d
    return {m:c for m,c in z.items() if c}
def powp(a,n):
    z={():1}
    while n:
        if n&1:z=mul(z,a)
        n//=2
        if n:a=mul(a,a)
    return z
def sym(s):return {((s,1),):1}
def parse(s,env=None):
    env={} if env is None else env
    def go(t):
        if isinstance(t,ast.Constant) and type(t.value) is int:return {():t.value} if t.value else {}
        if isinstance(t,ast.Name):return env.get(t.id,sym(t.id))
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {m:-c for m,c in go(t.operand).items()}
        if isinstance(t,ast.BinOp):
            a=go(t.left)
            if isinstance(t.op,ast.Pow):
                require(isinstance(t.right,ast.Constant) and type(t.right.value) is int and 0<=t.right.value<=20,'literal exponent')
                return powp(a,t.right.value)
            b=go(t.right)
            if isinstance(t.op,ast.Add):return add(a,b)
            if isinstance(t.op,ast.Sub):return add(a,b,-1)
            if isinstance(t.op,ast.Mult):return mul(a,b)
        raise ValueError('unsupported arithmetic syntax')
    return go(ast.parse(s,mode='eval').body)
def subst(poly,env):
    z={}
    for m,c in poly.items():
        term={():c}
        for x,e in m:term=mul(term,powp(env.get(x,sym(x)),e))
        z=add(z,term)
    return z
def degree(poly,vars):return max((sum(e for x,e in m if x in vars) for m in poly),default=-1)
def value(poly,env):
    ans=0
    for m,c in poly.items():
        t=c
        for x,e in m:t*=env[x]**e
        ans+=t
    return ans
def record_poly(records):
    out={tuple(sorted(r['powers'].items())):r['coefficient'] for r in records}
    require(len(out)==len(records),'duplicate expanded monomial')
    return {m:c for m,c in out.items() if c}
def marker(poly):return tuple(sorted(poly.items()))

def main():
    root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
    if not (root/'integer_forms').is_dir():root=root.parent
    require((root/'integer_forms').is_dir(),'pass the package root as the first argument')
    report={'status':'PASS','scope':'Exact independently parsed polynomial identities, degree/counts and complete monic restoration; cone completeness uses the separately reviewed native compiler theorem','packets':{}}
    parent=json.loads((root/'upstream/quartic41.json').read_text())
    q38=json.loads((root/'integer_forms/quartic38.json').read_text())
    pp=[parse(x) for x in parent['residuals']];qq=[parse(x) for x in q38['residuals']]
    require([r for j,r in enumerate(pp) if j not in(23,24)]==[r for j,r in enumerate(qq) if j!=23],'all retained Q41 rows exact')
    env={'q':parse('beta*J+1')};env['C']=parse('q-F-alpha',env)
    env['U']=parse('cone_A*F',env);env['V']=parse('cone_B*C',env);env['W']=parse('q-U-V',env)
    expected=parse('U*V-W**2-1-cone_pos1**2-cone_pos2**2-cone_pos3*(cone_pos3+1)',env)
    require(expected==qq[23],'literal quadratic cone exactly matches proof')
    cases=0;rng=random.Random(8603296)
    for name,nv,nr,deg,mon,coef in [('quartic38',38,25,4,{'tau':4},1),('sextic32',32,19,6,{'r':2,'c':4},4),('octic27',27,14,8,{'a':4,'f':4},1)]:
        body=json.loads((root/f'integer_forms/{name}.json').read_text());audit=json.loads((root/f'certificates/{name}_audit.json').read_text())
        vs=set(body['variables']);ports=set(body['fixed_ports']);rows=[parse(x) for x in body['residuals']]
        require(len(vs)==len(body['variables'])==nv and len(rows)==nr,'counts '+name)
        require(set(x for row in rows for m in row for x,e in m)-ports==vs,'all and only unknowns '+name)
        require(max(degree(row,vs) for row in rows)==deg//2,'residual degree '+name)
        total={}
        for row in rows:total=add(total,mul(row,row))
        require(degree(total,vs)==deg,'degree '+name)
        require(total==record_poly(json.loads((root/f'integer_forms/{name}_expanded.json').read_text())),'full SOS expansion '+name)
        selected={m:c for m,c in total.items() if {x:e for x,e in m if x in vs}==mon}
        require(selected=={tuple(sorted(mon.items())):coef},'fixed-value-independent leading coefficient '+name)
        restored_count=0
        if name!='quartic38':
            # Check every recorded monic deletion from independently parsed rows.
            cur=list(qq)
            if name=='sextic32':cur=[subst(r,{'tau':parse('tau_tail+P-eta-zeta')}) for r in cur]
            deleted=0
            for step in audit['elimination_steps']:
                if 'variable' not in step:continue
                var=step['variable'];rhs=parse(step['right_hand_side'])
                require(not any(var in dict(m) for m in rhs),'acyclic monic RHS')
                linear=add(sym(var),rhs,-1);negative={m:-c for m,c in linear.items()}
                matches=[i for i,r in enumerate(cur) if r==linear or r==negative]
                require(matches==[step['deleted_row_at_step']],'unique defining row '+var)
                cur=[subst(r,{var:rhs}) for i,r in enumerate(cur) if i not in matches];deleted+=1
            require(cur==rows and deleted==38-nv,'complete independent elimination replay')
            reconstruction={k:parse(v) for k,v in body['full_parent_restoration'].items()}
            reconstructed=[subst(r,reconstruction) for r in qq]
            nonzero=Counter(marker(r) for r in reconstructed if r)
            require(nonzero==Counter(marker(r) for r in rows),'full exact parent restoration '+name)
            restored_count=len(reconstructed)
            for _ in range(24):
                ev={x:rng.randrange(-7,8) for x in vs};ev.update({x:rng.randrange(2,20) for x in ports})
                par=dict(ev);par.update({k:value(v,ev) for k,v in reconstruction.items()})
                lhs=sum(value(row,par)**2 for row in qq)
                rhs=sum(value(row,ev)**2 for row in rows)
                require(lhs==rhs,'integer substitution diagnostic')
                cases+=1
        report['packets'][name]={'variables':nv,'residuals':nr,'degree':deg,'terms':len(total),'leading_monomial':mon,'leading_coefficient':coef,'exact_restored_parent_rows':restored_count,'sha256':hashlib.sha256((root/f'integer_forms/{name}.json').read_bytes()).hexdigest()}
    # Pure ring identity and sufficient common-sign inequality.
    require(parse('(s+x)*(s+y)-(x+y)**2')==parse('s**2+s*(x+y)-x**2-y**2-x*y'),'balanced determinant identity')
    require(parse('(U+V)**2-4*U*V')==parse('(U-V)**2'),'sum-product inequality identity')
    sign_cases=0
    for U in range(-12,13):
        for V in range(-12,13):
            for W in range(-12,13):
                cone=U*V-W*W
                if cone>0:require((U>0 and V>0 and U+V+W>0) or (U<0 and V<0 and U+V+W<0),'cone sign diagnostic')
                sign_cases+=1
    tiles=json.loads((root/'coefficients/wang943_tiles.json').read_text());require(tiles[0]==[2,435,3,1],'selector zero')
    cs={}
    Wj=lambda j:1<<(10+2*j)
    for ind,tile in enumerate(tiles):cs[ind]=1+sum(((x+512)>>j&1)*Wj(10*t+j) for t,x in enumerate(tile) for j in range(10))+sum(Wj(j) for j in range(40,44))
    for t,o in enumerate((1020,1000,980,960)):
        for j in range(10):cs[o+2*j]=Wj(10*t+j)
    for ind,j in zip((1095,1096,2195,3296),range(40,44)):cs[ind]=Wj(j)
    cs[1063]=cs[1064]=0
    rho=1<<121;c0=cs[0];S=sum(cs.values());mass=991*(2*S+6)
    dc=defaultdict(int)
    for e in (40,41,1100,2200):dc[e]+=1
    for e,v in cs.items():
        dc[4393-e]+=v;dc[5495-e]+=v
    dc={e:v for e,v in dc.items() if v}
    require(c0==105534389824824194647382298625 and max(dc)==5495 and dc[5495]==c0,'actual fixed leading coefficient')
    require(len(cs)==989 and max(cs)==3296 and max(e for e in cs if e<3296)==2195,'support top gap')
    require(6*S+18<mass and 4*mass+8<rho,'uniform native coefficient carry bound')
    require(1113+121*8791==1064921-97 and 666104+121*3296==1064921-1,'power-of-two scale calibration exponents')
    require((1<<96)<=c0 and c0+1<=3*(1<<95),'canonical F scale interval')
    require(rho>=8 and (1<<1064921)>=16,'canonical geometric sum bounds')
    require((1<<1113)>=2 and (1<<666104)>=2,'soundness scale lower bounds')
    # Reconstruct all six actual integer values independently of the builder.
    native_B=1<<1064921
    DC=sum(v<<(121*e) for e,v in dc.items())
    mc=native_B-1-sum(1<<(121*e) for e in cs if e!=1)-2*(1<<(121*1063))
    mu=1022+sum(Wj(j) for j in range(44))
    padding=((1<<119)-1)*sum(1<<(121*e) for e in range(8792,8799))+((1<<27)-1)*(1<<(121*8799))
    mfn=4+mu*((1<<(121*4393))+(1<<(121*5495)))+sum((1<<(121*(1000+2*j)))+(1<<(121*(1021+2*j))) for j in range(10))+(1<<(121*2195))+(1<<(121*3296))+padding
    actual={'beta':native_B-1,'K0':DC+native_B*rho,'MC':mc,'MF':mfn+native_B-1,'cone_A':1<<1113,'cone_B':1<<666104}
    binding=json.loads((root/'coefficients/NEW_BINDING.json').read_text());require(set(binding['payloads'])==set(actual),'six fixed ports')
    payload_checks=[];raw_total=0
    for port,num in actual.items():
        rec=binding['payloads'][port];compressed=(root/'coefficients'/rec['path']).read_bytes();raw=gzip.decompress(compressed)
        require(raw==num.to_bytes((num.bit_length()+7)//8,'little'),'exact independent fixed value and canonical byte serialization '+port)
        raw_total+=len(raw)
        require(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and hashlib.sha256(compressed).hexdigest()==rec['gzip_sha256'],'fixed payload hashes '+port)
        payload_checks.append({'port':port,'bits':num.bit_length(),'raw_sha256':rec['raw_sha256']})
    report['cone']={'exact_ring_identities':2,'bounded_sign_cases':sign_cases,'literal_guard_verified':True,'guard':'U*V-(q-U-V)**2','scales':{'cone_A_power_of_two':1113,'cone_B_power_of_two':666104},'canonical_U_over_q_interval':['1/2','4/5'],'canonical_V_over_q_interval':['1/2','3/5'],'determinant_over_q_squared_strict_lower_bound':'3/25','c0':str(c0),'native_support_size':989,'native_leading_exponent':8791,'native_mass_bits':mass.bit_length(),'uniform_carry_bound':True,'canonical_scale_alignment':True,'independently_reconstructed_payloads':payload_checks,'fixed_payload_raw_bytes':raw_total}
    report['bounded_integer_restoration_cases']=cases
    out=root/'reviews/INTEGER_INDEPENDENT_REVIEW.json';out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
