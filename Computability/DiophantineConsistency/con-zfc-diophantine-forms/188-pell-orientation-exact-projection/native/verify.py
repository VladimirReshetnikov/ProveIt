#!/usr/bin/env python3
"""Independent literal-circuit, coefficient, and exact-degree verification.

This checker does not import the producer. Finite diagnostics verify the
transcription; PROOF.md supplies the unbounded mathematical argument.
"""
from pathlib import Path
from collections import Counter
import ast,gzip,hashlib,json,random

ROOT=Path(__file__).resolve().parent

def need(value,message):
    if not value:raise ValueError(message)

def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if not out[m]:del out[m]
    return out

def mul(a,b):
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(x+y for x,y in zip(ma,mb))
            out[m]=out.get(m,0)+ca*cb
    return {m:c for m,c in out.items() if c}

def poly_ring(names):
    zero=(0,)*len(names)
    def constant(n):return {zero:n} if n else {}
    atoms={}
    for i,name in enumerate(names):
        powers=[0]*len(names);powers[i]=1;atoms[name]={tuple(powers):1}
    def power(a,n):
        out=constant(1)
        for _ in range(n):out=mul(out,a)
        return out
    def expression(text):
        def visit(node):
            if isinstance(node,ast.Constant) and type(node.value)is int:return constant(node.value)
            if isinstance(node,ast.Name):return atoms[node.id]
            if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return add({},visit(node.operand),-1)
            if isinstance(node,ast.BinOp):
                if isinstance(node.op,ast.Pow):
                    need(isinstance(node.right,ast.Constant) and type(node.right.value)is int and node.right.value>=0,'Nonpolynomial exponent')
                    return power(visit(node.left),node.right.value)
                a,b=visit(node.left),visit(node.right)
                if isinstance(node.op,ast.Add):return add(a,b)
                if isinstance(node.op,ast.Sub):return add(a,b,-1)
                if isinstance(node.op,ast.Mult):return mul(a,b)
            raise ValueError('Unsupported polynomial syntax')
        return visit(ast.parse(text,mode='eval').body)
    return constant,atoms,power,expression

def eval_graph(g,inputs):
    env=dict(inputs)
    for n,op,a,b in g['source']:
        a=a if isinstance(a,int) else env[a];b=b if isinstance(b,int) else env[b]
        env[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return env

def verify_topology(g):
    known=set(g['witnesses'])|set(g['fixed_numerals']);parents={}
    need(len(g['witnesses'])==14 and len(set(g['witnesses']))==14,'Fourteen distinct witnesses required')
    need(g['witness_domain']=='strictly positive integers','Domain mismatch')
    for n,op,a,b in g['source']:
        need(n not in known and op in ['+','-','*'],'Invalid producer')
        for x in [a,b]:need(type(x)is int or x in known,'Nonintegral leaf or forward reference')
        known.add(n);parents[n]=[a,b]
    live=set()
    def mark(x):
        if type(x)is int or x in live:return
        live.add(x)
        for y in parents.get(x,[]):mark(y)
    mark(g['output']);need(known==live,'Dead input, port, or producer')
    need(g['operations']==len(g['source']),'Operation metadata mismatch')
    need(g['operation_counts']==dict(Counter(r[1] for r in g['source'])),'Operation split mismatch')
    return parents

def verify_cuts(g,ordinary):
    aliases={'qm':'q1','ell':'L','D':'D','I':'I','Ns':'Ns'} if ordinary else {'qm':'qm','ell':'ell','D':'main_root','I':'normalized_S','Ns':'scaled_Ns'}
    # Every name in a formula is an input or a previously authenticated display cut.
    specs=[('qm','beta*J'),('q','qm+1'),('C','q-F-alpha'),('X','w*q'),('Y','s*q**3'),
           ('E','X*Y'),('k','eta+zeta'),('ell','E*k*Y'),('c','k*Y+eta'),
           ('a','E+Y'),('H','4*a+3'),('Delta','a**2+H'),('D','X+a*c+gamma*H'),
           ('R','(qm*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J'),
           ('tau','E*n+k-R'),('V','f**2*(c*T-R)-c'),
           ('I','i*c**2' if ordinary else 'i*Delta*c**2'),('Aaux','Delta*(f**2-1)'),
           ('N0','tau**2-ell*(ell+k)'),('N1','D**2-Delta*c**2'),
           ('Na','Aaux*(V**2-y**2)+y**2'),('Nt','(K0+w)*C+(q-F)-z*qm'),
           ('Ns','1+I**2-Aaux' if ordinary else 'Delta*f**2-I**2'),
           ('polynomial','N0*N1*Na*Nt*Ns-1' if ordinary else 'N0*N1*Na*Nt*Ns-Delta')]
    names=g['witnesses']+g['fixed_numerals']+[n for n,_ in specs]
    need(len(names)==len(set(names)),'Cut names overlap')
    constant,atoms,power,expr=poly_ring(names)
    rows={r[0]:r for r in g['source']};stops={n:atoms[n] for n in g['witnesses']+g['fixed_numerals']};covered=set()
    for cut,formula in specs:
        actual=aliases.get(cut,cut)
        cache={}
        def expand(x):
            if type(x)is int:return constant(x)
            if x in stops:return stops[x]
            if x in cache:return cache[x]
            _,op,a,b=rows[x];covered.add(x)
            aa,bb=expand(a),expand(b)
            cache[x]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
            return cache[x]
        need(expand(actual)==expr(formula),'Displayed formula mismatch: '+cut)
        stops[actual]=atoms[cut]
    need(covered==set(rows),'Uncovered circuit rows')
    return len(specs)

def verify_degree(g,ordinary):
    names=g['witnesses']+g['fixed_numerals'];nw=len(g['witnesses'])
    constant,atoms,power,expr=poly_ring(names)
    rows={r[0]:r for r in g['source']};full=dict(atoms)
    def expand(x):
        if type(x)is int:return constant(x)
        if x in full:return full[x]
        _,op,a,b=rows[x];aa,bb=expand(a),expand(b)
        full[x]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
        return full[x]
    def top(p):
        degree=max(sum(m[:nw]) for m in p)
        return degree,{m:c for m,c in p.items() if sum(m[:nw])==degree}
    main=expand('N1')
    env={n:(1 if j<nw else 0,p) for j,(n,p) in enumerate(atoms.items())}
    for n,op,a,b in g['source']:
        da,aa=(0,constant(a)) if type(a)is int else env[a]
        db,bb=(0,constant(b)) if type(b)is int else env[b]
        if n=='N1':env[n]=top(main)
        elif op=='*':env[n]=(da+db,mul(aa,bb))
        else:
            degree=max(da,db)
            out=add(aa if da==degree else {},bb if db==degree else {},1 if op=='+' else -1)
            need(bool(out),'Unresolved leading cancellation at '+n)
            env[n]=(degree,out)
    expected=expr('-8*(beta*J)**51*gamma*i**2*(eta+zeta)**9*w**6*s**15*T**2*f**6*(w*(beta*J-F-alpha)-z*beta*J)' if ordinary else '8*(beta*J)**67*gamma*i**2*(eta+zeta)**9*w**10*s**19*T**2*f**6*(w*(beta*J-F-alpha)-z*beta*J)')
    degree=94 if ordinary else 118
    need(env['polynomial']==(degree,expected),'Complete leading homogeneous form mismatch')
    need(g['exact_degree']==degree,'Degree metadata mismatch')
    nz={'J':52 if ordinary else 68,'beta':52 if ordinary else 68,'gamma':1,'i':2,'eta':9,'w':6 if ordinary else 10,'s':15 if ordinary else 19,'T':2,'f':6,'z':1}
    mon=tuple(nz.get(n,0) for n in names)
    need(expected[mon]==(8 if ordinary else -8),'Selected coefficient mismatch')
    strong='Ns' if ordinary else 'scaled_Ns'
    return {'degree':degree,'factor_degrees':{n:env[n][0] for n in ['N0','N1','Na','Nt',strong]},
            'complete_leading_terms':len(expected),'expanded_main_norm_terms':len(main),
            'selected_nonzero_coefficient':('8*beta^52' if ordinary else '-8*beta^68')}

def scalar_formula(v,ordinary):
    J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma=[v[k] for k in ['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']]
    q=v['beta']*J+1;C=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta
    ell=E*k*Y;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H;D=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(v['MC']+q*v['MF'])*J
    tau=E*n+k-R;V=f*f*(c*T-R)-c;I=i*c*c*(1 if ordinary else Delta)
    Aaux=Delta*(f*f-1);N0=tau*tau-ell*(ell+k);N1=D*D-Delta*c*c
    Na=Aaux*(V*V-y*y)+y*y;Nt=(v['K0']+w)*C+q-F-z*(q-1)
    Ns=1+I*I-Aaux if ordinary else Delta*f*f-I*I
    return N0*N1*Na*Nt*Ns-(1 if ordinary else Delta)

def coefficient_audit():
    manifest=json.loads((ROOT/'coefficients.json').read_text());values={};size=0
    for port,r in manifest['ports'].items():
        compressed=(ROOT/'coefficients'/r['file']).read_bytes()
        raw=gzip.decompress(compressed)
        need(hashlib.sha256(compressed).hexdigest()==r['gzip_sha256'],'Compressed coefficient mismatch')
        need(hashlib.sha256(raw).hexdigest()==r['raw_sha256'],'Raw coefficient mismatch')
        need(len(raw)==r['raw_bytes'],'Coefficient length mismatch')
        values[port]=int.from_bytes(raw,'big');need(values[port].bit_length()==r['bits'],'Coefficient bit length')
        size+=len(raw)
    b,K,MC,MF=[values[n] for n in ['beta','K0','MC','MF']]
    need(b==2**(47*2963)-1,'Exact beta mismatch')
    need(b>=31 and K>0 and 0<MC<b<MF<2*b,'Scalar coefficient boxes')
    native=MF-b
    need(MC%4==2 and native%8==4,'Native low residues')
    need(MC.bit_count()+native.bit_count()==47*2963,'Native mask population')
    rho=2**47; G=lambda m:sum(rho**j for j in range(m))
    need(MC==b-G(951)-rho**960*G(26)-rho**1005,'Printed MC recipe mismatch')
    need(MF==b+4*G(917)+(2**44-2)*rho**1956+rho**960*G(9)+rho**987*G(8)+rho**1005,'Printed MF recipe mismatch')
    need(size==69685,'Complete byte count')
    return {'ports':4,'raw_bytes':size,'scalar_boxes':'PASS','mask_population':47*2963,'MC_MF_closed_recipes':'PASS','K_scope':'Authenticated exact pinned payload; native semantic proof retained, not newly replayed.'}

def main():
    provenance=json.loads((ROOT/'SOURCE_PROVENANCE.json').read_text())
    for record in provenance['sources']:
        raw=(ROOT/record['local']).read_bytes()
        need(len(raw)==record['bytes'] and hashlib.sha256(raw).hexdigest()==record['sha256'],
             'Retained source hash mismatch: '+record['local'])
    parent=json.loads((ROOT/'sources/one-page-block-mask2963_polynomial.json').read_text())
    binding=parent['coefficient_binding']
    for name,key in [('low-padding-independent_PROOF.md','ordinary_proof_sha256'),
                     ('low-padding-independent_certificate.json','certificate_sha256')]:
        need(hashlib.sha256((ROOT/'sources'/name).read_bytes()).hexdigest()==binding[key],
             'Parent-bound native proof/certificate hash mismatch')
    result={'status':'PASS','authenticated_source_records':len(provenance['sources']),
            'coefficient_audit':coefficient_audit(),'circuits':{}}
    rng=random.Random(20261025)
    for name,ordinary in [('q66_d118',False),('q67_d94',True)]:
        raw=(ROOT/'circuits'/(name+'.json')).read_bytes();g=json.loads(raw)
        verify_topology(g);cuts=verify_cuts(g,ordinary);degree=verify_degree(g,ordinary)
        for _ in range(64):
            values={n:rng.randrange(-4,6) for n in g['witnesses']+g['fixed_numerals']}
            need(eval_graph(g,values)['polynomial']==scalar_formula(values,ordinary),'Whole scalar formula mismatch')
        # Prove the strong unit exclusion by its complete residue table.
        strong_residues=sorted({(1+ii-dd*(ff-1))%4 for ii in [0,1] for dd in [0,3] for ff in [0,1]})
        need(3 not in strong_residues,'Ordinary strong sign failure')
        result['circuits'][name]={'sha256':hashlib.sha256(raw).hexdigest(),'positive_unknowns':14,
            'operations':len(g['source']),'operation_counts':g['operation_counts'],'all_inputs_ports_gates_live':True,
            'exact_display_cut_identities':cuts,'signed_formula_diagnostics':64,'ordinary_strong_residues_mod4':strong_residues,**degree}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
