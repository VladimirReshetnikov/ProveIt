#!/usr/bin/env python3
"""Independent arithmetic/formula/degree checks for index-modulus rebasing.

Uses no producer import and does not search for a Diophantine zero.
"""
import argparse,ast,copy,gzip,hashlib,importlib.util,itertools,json
from collections import Counter
from pathlib import Path
from exact_polynomial import Ring

ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
SPECS={
 'integer11_degree298_ops146':(None,298,146),
 'integer11_degree300_ops144':(None,300,144),
}

def need(ok,msg):
    if not ok:raise ValueError(msg)

def scalar_formulas(p):
    rebased=p['rebased']
    return [
    ('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('q3','q*q*q'),
    ('W','12*w+4'),('X','q*W'),('Y','v'),('E','X*Y'),('ell','X*Y*Y'),
    ('a','E+Y'),('H','4*a+3'),('Delta','a*a+H'),('A','a+2'),
    ('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J'),
    ('k','R+1+h*ell' if rebased else 'R+1+h*E'),('c2','c*c'),('Yk','Y*k'),('eta','c-Yk'),
    ('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('Yeta','Y*eta'),('kq2','k*q2' if rebased else 'k*q3'),
    ('Budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**'+str(6 if rebased else 8)),
    ('L','E*Y*k'),('Dt','1+L*(L+k)'),('Dguard','Budget-4'),
    ('Pg','Dt*s'),('P','Dt+(Budget-4)*Dt*Dt*s*s'),('Dm','1+Delta*c*c'),
    ('rDm','r*Dm'),('B','A*rDm'),('U','c*c*rDm'),('AU','A*U'),
    ('strong','Delta*c*c*AU'),('Df','strong+1'),('Q','Delta*strong'),
    ('delta','Q-1'),('b','c-R+4*AU*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),
    ('K','X*(3*c-2*X)+2'),('M','2*q3'),('Dc','M*H'),('M2','M*M'),
    ('M4','M**4'),('Dc2','Dc*Dc'),('Dc3','Dc**3'),('S','s*r*H*M**5'),
    ('S2','S*S'),('zc','Dc*T+M*K+H*(v-q3)'),('zc2','zc*zc'),
    ('Ac','(zc*zc+3*Dc*Dc)*(zc**3-19*Dc**3)'),('c4','c2*c2'),
    ('rc4','r*c4'),('U2','U*U'),('UT','U2*T'),('cm2','c2-2'),
    ('AD','A*Delta'),('gamma','8*Delta+4'),('lam','4*(gamma*U-rc4)'),
    ('residual','gamma*(c2-2)-c2'),('core','rc4*(c2-2)+8*A'),
    ('corr','rc4*residual+64*A*Delta' if rebased else '(gamma-1)*(rc4*(c2-2)+8*A)'),('Psi','lam*V+UT*corr'),
    ('Z','S*(n+Psi)-Ac'),('Z2','Z*Z'),('pa','delta*Z2'),('pb','delta*S2*P'),
    ('pc','1024*S2*B*Df*Cy'),('inner','pa+pb-pc'),
    ('output','inner*inner-4*pa*pb')]

def formulas(p):
    return scalar_formulas(p)

def local_checks(p):
    nodes=p['nodes'];nm=dict(p['named_registers'])
    nm.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ('variable','coefficient')})
    nm['output']=p['output'];covered=set()
    for name,expr in formulas(p):
        if name not in nm:continue
        tree=ast.parse(expr,mode='eval')
        refs=sorted({n.id for n in ast.walk(tree) if isinstance(n,ast.Name)})
        ring=Ring(refs);env={n:ring.var(n) for n in refs}
        memo={nm[n]:v for n,v in env.items()}
        def rec(i):
            covered.add(i)
            if i in memo:return memo[i]
            row=nodes[i]
            if row[0]=='integer':val=ring.scalar(row[1])
            else:
                need(row[0] in ('add','sub','mul'),'unbound local leaf '+str(row))
                a,b=rec(row[1]),rec(row[2]);val=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
            memo[i]=val;return val
        expected=eval(expr,{'__builtins__':{}},env)
        need(rec(nm[name]).terms==expected.terms,'free-ring register '+name)
    missing=[i for i,r in enumerate(nodes) if r[0] in ('add','sub','mul') and i not in covered]
    need(not missing,'unbound live arithmetic gates '+str(missing))
    return {'bound_arithmetic_gates':sum(r[0] in ('add','sub','mul') for r in nodes)}

def universal():
    rr=Ring(['Y','k','q','e','D']);Y,k,q,e,D=[rr.var(n) for n in rr.names]
    B0=k*k*(q*q-D)-4*q*q*e*e
    need(not (Y*Y*B0-k*k*q**6-((Y*k)**2*(q*q-D)-q*q*(4*(Y*e)**2+(k*q*q)**2))).terms,'new budget identity')
    rr=Ring(['b','d','e','s']);b,d,e,s=[rr.var(n) for n in rr.names]
    G=4*b+1;K=d*(s*(s+1)-b)-e;N=K*K-G*d*e;x=2*s+1
    need(not (16*N-((d*(x*x+G)-4*e)**2-4*d*d*x*x*G)).terms,'primitive odd carrier')
    rr=Ring(['delta','S','W','Psi','P','BF','Cy']);delta,S,W,Psi,P,BF,Cy=[rr.var(n) for n in rr.names]
    inner=delta*(W+S*Psi)**2+delta*S*S*P-1024*S*S*BF*Cy
    cut=delta*W*W+2*delta*S*Psi*W+delta*S*S*P+S*S*(delta*Psi*Psi-1024*BF*Cy)
    need(not(inner-cut).terms,'arbitrary center identity')
    cases=0
    for q,k,Y,u,v,eta in itertools.product(range(0,16,2),range(4),range(4),range(2),range(2),range(4)):
        b0=k*k*(q*q-(16*u-q)**2-(16*v-q)**2)-4*q*q*eta*eta
        for exponent in (6,8):
            need((Y*Y*b0-k*k*q**exponent-4)%16 in (8,12),'unchanged nonsquare parity')
            cases+=1
    return {'new_budget_identity':True,'primitive_odd_identity':True,'norm_center_identity':True,'mod16_exhaustive_residue_cases':cases}

def center(rebased):
    rr=Ring(['A','c','r','T','R']);A,c,r,T,R=[rr.var(n) for n in rr.names]
    D=A*A-1;Dm=1+D*c*c;B=r*A*Dm;U=r*c*c*Dm
    F=1+D*c**4*B;Q=D*D*c**4*B;V=F*(c-R+4*A*U*T)-c
    parent=((32*D+16)*U-4*r*c**4)*V+U**2*T*(8*U*(c*c-2)+64*A**3+3*r*c**6-(16*r*c**4 if rebased else 0))
    Psi=4*((8*D+4)*U-r*c**4)*V+U**2*T*(r*c**4*((8*D+4)*(c*c-2)-c*c)+64*A*D if rebased else (8*D+3)*(r*c**4*(c*c-2)+8*A))
    eps=U**2*T*(16*r*c*c-(64 if rebased else 40)*A-(0 if rebased else 14*r*c**4))
    need(not(Psi-parent-eps).terms,'exact integral-center shear')
    DD=Psi*Psi-1024*B*F*V*V
    EE=(Q-1)*DD-1024*B*F*(V*V-1)
    need(not(EE-((Q-1)*Psi*Psi-1024*B*F*(Q*V*V-1))).terms,'center two expressions')
    weights=[3,1,1,1,5]
    if rebased:
        dtop=512*A**15*c**24*r**5*T*R-8192*A**17*c**22*r**5*T*T
        etop=512*A**22*c**30*r**6*T*R-24576*A**24*c**28*r**6*T*T
        ddeg,edeg,epsdeg=80,108,26
    else:
        dtop=512*A**16*c**26*r**6*T*T
        etop=512*A**23*c**32*r**7*T*T
        ddeg,edeg,epsdeg=82,110,28
    need(DD.weighted_degree(weights)==ddeg and DD.homogeneous(weights,ddeg)==dtop.terms,'exact Dcenter remainder')
    need(EE.weighted_degree(weights)==edeg and EE.homogeneous(weights,edeg)==etop.terms,'exact Ecenter remainder')
    need(Psi.weighted_degree(weights)==54 and eps.weighted_degree(weights)==epsdeg,'center and shear degrees')
    return {'rebased':rebased,'weights':weights,'variables':rr.names,'pre_auxiliary_degree':ddeg,'remainder_degree':edeg,
            'shear_degree':epsdeg,'Dcenter':[[list(m),v] for m,v in sorted(DD.terms.items())],
            'Ecenter':[[list(m),v] for m,v in sorted(EE.terms.items())],
            'top_terms':[[list(m),v] for m,v in sorted(etop.terms.items())]}

def topology(p):
    ns=p['nodes'];live=set();todo=[p['output']];degrees=[]
    for i,r in enumerate(ns):
        if r[0] in ('add','sub','mul'):
            need(len(r)==3 and all(type(j)==int and 0<=j<i for j in r[1:]),'acyclic arithmetic')
            degrees.append(degrees[r[1]]+degrees[r[2]] if r[0]=='mul' else max(degrees[r[1]],degrees[r[2]]))
        else:
            need(r[0] in ('integer','variable','coefficient'),'unknown leaf');degrees.append(int(r[0]=='variable'))
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if ns[i][0] in ('add','sub','mul'):todo.extend(ns[i][1:])
    need(live==set(range(len(ns))),'liveness')
    need(set(r[1] for r in ns if r[0]=='variable')==set(p['variables']),'variable list')
    need(len(p['variables'])==p['variable_count'],'variable count')
    need(set(r[1] for r in ns if r[0]=='coefficient')==set(PORTS),'six fixed coefficients')
    cnt=Counter(r[0] for r in ns if r[0] in ('add','sub','mul'))
    need(dict(cnt)==p['operation_counts'] and sum(cnt.values())==p['operations']==SPECS[p['name']][2],'operation count')
    need(p['exact_degree']==SPECS[p['name']][1],'declared degree')
    return {'nodes':len(ns),'operations':sum(cnt.values()),'syntactic_degree':degrees[p['output']]}

def leading(p):
    scalar=True;rebased=p['rebased']
    order=['T','j','w','v','h','s','r','c','C','z','n'] if scalar else [n for n in ['n','T','f','y','s','j','w','v','h','z','C','r','c','p1','p2','p3'] if n in p['variables']]
    need(set(order)==set(p['variables']),'degree variable order')
    cr=Ring(PORTS);zero=(0,)*len(order);values=[];nm=p['named_registers'];ledger=[]
    def key(v):return (sum(v[0]),)+v[0]
    def times(a,b):return (tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
    def plus(a,b,minus=False):
        if key(a)>key(b):return a
        if key(a)<key(b):return (b[0],-b[1] if minus else b[1])
        return (a[0],a[1]-b[1] if minus else a[1]+b[1])
    def product(*args):
        out=(zero,cr.scalar(1))
        for a in args:out=times(out,values[nm[a]] if isinstance(a,str) else (zero,cr.scalar(a)))
        return out
    for i,row in enumerate(p['nodes']):
        if scalar and i==nm['inner']:
            val=product(-24576,'S2',*(['A']*24),*(['c']*28),*(['r']*6),'T','T') if rebased else product(512,'S2',*(['A']*23),*(['c']*32),*(['r']*7),'T','T')
            need(sum(val[0])==(148 if rebased else 150),'proved inner degree')
        elif row[0]=='variable':
            ex=[0]*len(order);ex[order.index(row[1])]=1;val=(tuple(ex),cr.scalar(1))
        elif row[0]=='coefficient':val=(zero,cr.var(row[1]))
        elif row[0]=='integer':val=(zero,cr.scalar(row[1]))
        else:
            a,b=values[row[1]],values[row[2]]
            val=times(a,b) if row[0]=='mul' else plus(a,b,row[0]=='sub')
        need(bool(val[1].terms),'cancelled leading monomial at '+str(i))
        signs={1 if c>0 else -1 for c in val[1].terms.values()}
        need(len(signs)==1,'mixed-sign actual coefficient at '+str(i))
        values.append(val)
        ledger.append({'node':i,'exact_degree':sum(val[0]),'monomial':dict(zip(order,val[0])),
          'coefficient':[[list(m),str(c)] for m,c in sorted(val[1].terms.items())]})
    out=values[p['output']]
    need(sum(out[0])==p['exact_degree'],'exact total degree')
    need(sum(values[nm['pa']][0])==176 and sum(values[nm['pb']][0])==(122 if rebased else 124),'norm degree cuts')
    if rebased:
        expected={'T':2,'j':136,'w':46,'v':50,'h':0,'s':6,'r':12,'c':40,'C':0,'z':6,'n':0}
        expect=2**272*3**182*cr.var('beta')**136
    else:
        expected={'T':4,'j':110,'w':50,'v':50,'h':0,'s':4,'r':18,'c':64,'C':0,'z':0,'n':0}
        expect=2**256*3**160*cr.var('beta')**110
    need(dict(zip(order,out[0]))==expected,'actual top monomial')
    need(out[1].terms==expect.terms,'actual coefficient')
    return {'degree':sum(out[0]),'variable_order':order,'top_monomial':dict(zip(order,out[0])),
            'top_coefficient':[[list(m),str(c)] for m,c in sorted(out[1].terms.items())],
            'all_gate_leaders':ledger,
            'scalar_cancellation_cut':{'inner_degree':148 if rebased else 150,'remaining_terms_bound':137,'Ecenter_degree':108 if rebased else 110}}

def coefficient_check():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for path,pin in pins['dependencies'].items():
        data=(ROOT/path).read_bytes()
        need(len(data)==pin['bytes'] and hashlib.sha256(data).hexdigest()==pin['sha256'],'source bytes '+path)
    bind=json.loads((ROOT/'coefficients/BINDING.json').read_text());ports={}
    for name,pin in bind['payloads'].items():
        raw=gzip.decompress((ROOT/'coefficients'/pin['file']).read_bytes())
        need(hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'coefficient '+name)
        ports[name]=int.from_bytes(raw,'little')
        need(ports[name].bit_length()==pin['bits'],'coefficient bit length')
    need(all(v>0 for v in ports.values()),'positive fixed numerals')
    need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'closed numeral values')
    spec=importlib.util.spec_from_file_location('coefficient_recipe',ROOT/'coefficients/recipe/source34_builder.py')
    recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
    rebuilt,audit=recipe.construct()
    for a,b in [('beta','beta'),('K','K0'),('MC','MC'),('MF_source','MF')]:need(rebuilt[a]==ports[b],'finite coefficient recipe '+b)
    return {'authenticated_source_files':len(pins['dependencies']),'all_fixed_numerals_reconstructed':True,'recipe_audit':audit}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--receipt',type=Path);args=parser.parse_args()
    result={'status':'PASS','coefficients':coefficient_check(),'universal':universal(),'centers':[center(True),center(False)],'equations':[]}
    for name in SPECS:
        p=json.loads((ROOT/(name+'.json')).read_text())
        result['equations'].append({'name':name,'topology':topology(p),'formulas':local_checks(p),'degree':leading(p)})
    bad=[]
    for name,key in [(n,k) for n in SPECS for k in ['k','Budget','corr','gamma','lam','Psi','inner']]:
        p=json.loads((ROOT/(name+'.json')).read_text());row=p['nodes'][p['named_registers'][key]]
        row[0]='sub' if row[0]=='add' else 'add'
        try:local_checks(p)
        except ValueError:bad.append(name+':'+key)
        else:raise ValueError('failed corruption control '+key)
    result['rejected_corruptions']=bad
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','equations':[{k:r[k] for k in ['name','topology']}|{'degree':r['degree']['degree']} for r in result['equations']]},indent=2))

if __name__=='__main__':main()
