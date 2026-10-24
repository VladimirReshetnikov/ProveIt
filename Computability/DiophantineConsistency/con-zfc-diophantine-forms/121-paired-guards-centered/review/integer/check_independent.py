#!/usr/bin/env python3
"""Independent wave15 integer audit. No producer Python modules imported.
Finite exact algebra, topology, authenticated numeral reconstruction, and
specialization degree witnesses; not a proof-assistant certificate.
Requires SymPy; run this file with Python or Python -O.
"""
from pathlib import Path
import ast, copy, gzip, hashlib, itertools, json, math
from collections import Counter
import sympy as sp
from sympy.polys.rings import ring
from sympy.polys.domains import GF
ROOT=Path(__file__).resolve().parents[2]
SRC=ROOT/'integer'
OUT=Path(__file__).resolve().parent
VARS='j C z h r v w T c n s'.split()
PORTS='beta K0 MC MF cone_A cone_B'.split()
NAMES={'pair_fused11_rational':(820,119),'pair_fused11_integral':(964,118),'pair_fused11_rational_strong':(796,122),'pair_fused11_rational_sharp':(772,124),'optimized_guard_fused11_direct':(728,120),'optimized_guard_fused11_aux':(688,124),'optimized_fused11_rational':(1632,112),'optimized_fused11_integral':(1892,112)}
def require(x,msg):
    if not x: raise ValueError(msg)
def digest(x): return hashlib.sha256(x).hexdigest()
def identity(a,b,msg): require(sp.expand(a-b)==0,msg)
def topology(p):
    require(p['variables']==VARS and p['variable_count']==11,'eleven independent coordinates')
    nodes=p['nodes']; seen=[]
    for i,r in enumerate(nodes):
        require(r[0] in ['integer','coefficient','variable','add','sub','mul'],'literal primitive')
        if r[0] in ['add','sub','mul']:
            require(len(r)==3 and all(type(k)==int and 0<=k<i for k in r[1:]),'binary acyclic topology')
        elif r[0]=='integer': require(len(r)==2 and type(r[1])==int,'integer literal')
        else: require(len(r)==2,'leaf arity')
    require([r[1] for r in nodes if r[0]=='variable']==VARS,'coordinate leaves')
    require([r[1] for r in nodes if r[0]=='coefficient']==PORTS,'fixed coefficient leaves')
    todo=[p['output']]; live=set()
    while todo:
        i=todo.pop()
        if i in live: continue
        live.add(i)
        if nodes[i][0] in ['add','sub','mul']:todo+=nodes[i][1:]
    require(live==set(range(len(nodes))),'all nodes live')
    counts=Counter(r[0] for r in nodes if r[0] in ['add','sub','mul'])
    require(dict(counts)==p['operation_counts'] and sum(counts.values())==p['operations'],'literal gate count')
    return dict(counts)

def specification(p):
    # Transcribed from mathematical definitions, not from builders or checkers.
    common=[('J','6*j+1'),('qm','beta*J'),('q','beta*J+1'),('q2','q**2'),('q3','q**3'),('W','12*w+4'),('X','q*W'),('Y','(2*v+1)*q**3'),('E','X*Y'),('a','Y*(X+1)'),('H','4*a+3'),('Delta','(a+2)**2-1'),('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J'),('k','R+1+h*X*Y'),('c2','c**2'),('eta','c-Y*k'),('U','cone_A*F'),('Vc','cone_B*C'),('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('Budget','k**2*(q**2-Derr)-4*q**2*eta**2'),('ell','X*Y**2'),('L','ell*k'),('Dt','1+L*(L+k)'),('D','3*Budget-4'),('s2','2*s'),('Pg','2*s*Dt'),('P','Dt*(1+4*D*Dt*s**2)')]
    if p['name'].startswith('pair_'):
        common += [('A','a+2'),('Dm','1+Delta*c**2'),('Ib','s*r*c**2*Dm'),('I','2*s*r*c**2*A*Dm')]
    elif p['fused']:
        common += [('Amain','a+2'),('Dm','1+Delta*c**2'),('I','2*s*r*c**2*P*Dm*Amain')]
    else:common += [('I','2*s*r*c**2')]
    common += [('I2','I**2'),('strong','Delta*I**2'),('Df','1+Delta*I**2'),('Q','Delta**2*I**2'),('delta','Q-1'),('b','c-R+4*I*T'),('V','Df*(c-R+4*I*T)-c'),('Cy','Q*V**2-1'),('Da','(Q-1)*(Q*V**2-1)'),('K','X*(3*c-2*X)+2'),('H2','H**2'),('H3','H**3'),('H5','H**5'),('S','I*H**5'),('S2','S**2'),('zc','H*T+K'),('zc2','zc**2'),('Ac','(zc**2+3*H**2)*(zc**3-19*H**3)')]
    if p['name'].startswith('pair_'):
        if p['center']=='strong':common += [('shift','A*I*V')]
        elif p['center']=='sharp':common += [('lam','(2*Delta+1)*Ib'),('shift','lam*V')]
        common += [('Z','S*n-Ac' if p['center']=='none' else 'S*(n+shift)-Ac'),('Z2','Z**2')]
        if p['rational']:
            common += [('pa','delta*Z**2'),('pb','4*delta*S**2*P'),('pc','S**2*Df*Cy'),('rnorm','delta*Z**2+4*delta*S**2*P-S**2*Df*Cy'),('output','(delta*Z**2+4*delta*S**2*P-S**2*Df*Cy)**2-16*delta**2*S**2*P*Z**2')]
        else:common += [('ra','S**2*Df*Da'),('rb','4*S**2*P'),('rnorm','Z**2-S**2*Df*Da-4*S**2*P'),('output','(Z**2-S**2*Df*Da-4*S**2*P)**2-16*S**4*Df*Da*P')]
    elif p['fused']:
        common += [('Z','S*n-Ac'),('product','Df*P'),('output','delta*Z**2-S**2*Df*P*Cy' if p['rational'] else 'Z**2-S**2*Df*P*Da')]
    else:
        if p['center']!='direct':common += [('shift','(2*Q-1)*V')]
        common += [('Z','S*n-Ac' if p['center']=='direct' else 'S*(n+shift)-Ac'),('ra','S**2*Df'),('rb','4*S**2*Da'),('rc','16*S**2*P'),('Z2','Z**2'),('zp','Z**2*rb'),('ue','ra*rc'),('vnorm','Z**2+rb-ra-rc'),('ynorm','(Z**2+rb-ra-rc)**2-4*(Z**2*rb+ra*rc)'),('output','((Z**2+rb-ra-rc)**2-4*(Z**2*rb+ra*rc))**2-64*Z**2*rb*ra*rc')]
    return common

def exact_bindings(p):
    nodes=p['nodes']; named=dict(p['named_registers']);named['output']=p['output']
    named.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ['coefficient','variable']})
    coverage=set(); answers=[]
    for name,formula in specification(p):
        if name not in named:continue
        identifiers=sorted({n.id for n in ast.walk(ast.parse(formula,mode='eval')) if isinstance(n,ast.Name)})
        symbols={n:sp.Symbol(n) for n in identifiers}
        cuts={named[n]:symbols[n] for n in identifiers}
        def visit(i):
            coverage.add(i)
            if i in cuts:return cuts[i]
            row=nodes[i]
            if row[0]=='integer':v=sp.Integer(row[1])
            else:
                require(row[0] in ['add','sub','mul'],'unbound leaf '+name)
                a,b=visit(row[1]),visit(row[2])
                v=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
            cuts[i]=v;return v
        expected=eval(formula,{'__builtins__':{}},symbols)
        identity(visit(named[name]),expected,'formula mismatch '+name)
        answers.append(name)
    require(all(i in coverage for i,r in enumerate(nodes) if r[0] in ['add','sub','mul']),'all arithmetic semantically covered')
    return answers

def algebra():
    z,u,v,w=sp.symbols('z u v w')
    four=sp.prod(z+e*u+f*v for e,f in itertools.product([-1,1],repeat=2))
    identity(four,(z*z-u*u-v*v)**2-4*u*u*v*v,'all four factors')
    eight=sp.prod(z+e*u+f*v+g*w for e,f,g in itertools.product([-1,1],repeat=3))
    balanced=((z*z+v*v-u*u-w*w)**2-4*(z*z*v*v+u*u*w*w))**2-64*z*z*v*v*u*u*w*w
    identity(eight,balanced,'all eight factors and balanced evaluator')
    zz,aa,bb,ee=sp.symbols('zz aa bb ee')
    identity((zz**2+bb-aa-ee)**2-4*(zz**2*bb+aa*ee),(zz**2-bb-aa-ee)**2-4*(aa*ee+bb*(aa+ee)),'balanced octic cancellation cut')
    Z,S,d,F,C,P=sp.symbols('Z S d F C P')
    rat=(d*Z**2+4*d*S**2*P-S**2*F*C)**2-16*d*d*S*S*P*Z*Z
    old=(d*Z**2-S**2*F*C-4*d*S*S*P)**2-16*d*S**4*F*C*P
    identity(rat,old,'rational clearing identity')
    A,I,c,R,T,B=sp.symbols('A I c R T B');D=A*A-1;Df=1+D*I*I;Q=D*D*I*I;V=Df*(c-R+4*I*T)-c;Da=(Q-1)*(Q*V*V-1)
    rem=sp.rem(Da-A*A*(1+D*c*c),Df,I)
    identity(rem,0,'strong auxiliary congruence polynomial remainder')
    bb=c-R+4*I*T;Cy=Q*V*V-1
    identity(Da-A*A*(1+D*c*c),Df*D*(Cy-A*A*(V*V+bb*(c-V))),'integer quotient for strong auxiliary congruence')
    identity((1+D*(2*A*B)**2)-((2*D+1)*B)**2,1-B*B,'sharp center exact identity')
    identity((A*I)**2-Df,I**2-1,'strong center exact identity')
    SS,QQ,lam,VV,BB,FF,PP=sp.symbols('SS QQ lam VV BB FF PP')
    left=(QQ-1)*(BB+SS*lam*VV)**2+4*(QQ-1)*SS**2*PP-SS**2*FF*(QQ*VV**2-1)
    right=SS**2*(QQ*(lam**2-FF)-lam**2)*VV**2+SS**2*FF+2*(QQ-1)*SS*lam*VV*BB+(QQ-1)*BB**2+4*(QQ-1)*SS**2*PP
    identity(left,right,'pair diagnostic rnorm cancellation cut')
    Q,V,S=sp.symbols('Q V S')
    identity(4*S*S*(Q-1)*(Q*V*V-1)-(S*(2*Q-1)*V)**2,S*S*(-V*V-4*Q+4),'inherited centered cancellation')
    X,a,c=sp.symbols('X a c')
    identity((4*a+3)*X*c-2*(X*(X+2*a*c)-1),X*(3*c-2*X)+2,'short scalar projector')
    return {'four_conjugates':True,'eight_conjugates_and_balanced_identity':True,'rational_denominator_clearing':True,'Da_congruence_mod_Df':True,'centered_cancellations':True,'scalar_projector':True}

def coefficients():
    binding=json.loads((SRC/'coefficients/BINDING.json').read_text());vals={};cert={}
    for name in PORTS:
        data=gzip.decompress((SRC/'coefficients'/binding['payloads'][name]['file']).read_bytes());v=int.from_bytes(data,'little');b=binding['payloads'][name]
        require(digest(data)==b['raw_sha256'] and len(data)==b['raw_bytes'] and v.bit_length()==b['bits'],'actual coefficient payload '+name)
        vals[name]=v;cert[name]={'sha256':digest(data),'bits':v.bit_length()}
    # Independent finite reconstruction from the literal tile list, with no imports.
    tiles=json.loads((SRC/'coefficients/recipe/wang943_tiles.json').read_text());require(len(tiles)==943,'943 literal tiles')
    weights=[1<<(10+2*i) for i in range(44)]
    code={i:1+sum(weights[10*t+j] for t,label in enumerate(tile) for j in range(10) if (label+512)&(1<<j))+sum(weights[40:]) for i,tile in enumerate(tiles)}
    for t,offset in enumerate([1020,1000,980,960]):
        for j in range(10):code[offset+2*j]=weights[10*t+j]
    for j,k in enumerate([1095,1096,2195,3296]):code[k]=weights[40+j]
    code[1063]=code[1064]=0;require(len(code)==989,'989 support positions')
    dc=Counter({40:1,41:1,1100:1,2200:1})
    for e,value in code.items():
        for target in [4393,5495]:dc[target-e]+=value
    radixbits=121;L=8801;big=1<<(radixbits*L)
    DC=sum(value<<(radixbits*e) for e,value in dc.items())
    reconstructed={'beta':big-1,'K0':DC+(big<<radixbits),'MC':big-1-sum(1<<(radixbits*e) for e in code if e!=1)-(2<<(radixbits*1063)),'cone_A':1<<1113,'cone_B':1<<666104}
    mu=1022+sum(weights); native=4+(mu<<(radixbits*4393))+(mu<<(radixbits*5495))
    native+=sum(1<<(radixbits*(1000+2*j)) for j in range(10))+sum(1<<(radixbits*(1021+2*j)) for j in range(10))
    native+=(1<<(radixbits*2195))+(1<<(radixbits*3296))
    native+=sum(((1<<119)-1)<<(radixbits*e) for e in range(8792,8799))+(((1<<27)-1)<<(radixbits*8799))
    reconstructed['MF']=native+big-1
    require(all(vals[k]==reconstructed[k] for k in PORTS),'independently rebuilt all six numerals')
    return vals,cert

def degree_upper_bound(p):
    degrees=[];nm=p['named_registers'];cuts=[]
    def d(name):return degrees[nm[name]]
    for i,row in enumerate(p['nodes']):
        if p['name']=='optimized_guard_fused11_aux' and i==nm['ynorm']:
            # B=Sn-Ac; omega=(S*shift+B)^2-rb. The exact auxiliary
            # center identity gives deg omega <= max(2C0B,B²,S²V²,S²Q,S²).
            B=max(d('S')+1,d('Ac'))
            omega=max(d('S')+d('shift')+B,2*B,2*d('S')+2*d('V'),2*d('S')+d('Q'),2*d('S'))
            z=max(2*max(omega,d('ra'),d('rc')),d('ra')+d('rc'),d('rb')+d('ra'),d('rb')+d('rc'))
            require(omega==126 and z==344,'independent centered bound')
            cuts.append({'register':'ynorm','bound':z,'omega_bound':omega})
        elif p['name'] in ['pair_fused11_rational_strong','pair_fused11_rational_sharp'] and i==nm['rnorm']:
            B=max(d('S')+1,d('Ac'));tt='I' if p['center']=='strong' else 'Ib'
            lam=d('A')+d('I') if p['center']=='strong' else d('lam')
            # lambda²-Df=t²-1, with t=I or Ib, respectively.
            z=max(2*d('S')+max(d('Q')+2*d(tt),d('Q'),2*lam)+2*d('V'),2*d('S')+d('Df'),d('delta')+d('S')+lam+d('V')+B,d('delta')+2*B,d('delta')+2*d('S')+d('P'))
            cuts.append({'register':'rnorm','bound':z,'identity':'lambda^2-Df=t^2-1'})
        elif row[0]=='variable':z=1
        elif row[0] in ['coefficient','integer']:z=0
        elif row[0]=='mul':z=degrees[row[1]]+degrees[row[2]]
        else:z=max(degrees[row[1]],degrees[row[2]])
        degrees.append(z)
    require(degrees[p['output']]==NAMES[p['name']][0],'exact upper bound')
    return {'upper_bound':degrees[p['output']],'exact_cancellation_cuts':cuts}

def degree_witness(p,ports):
    # Exact specialization xi=(i+1)t over a finite field, using the ACTUAL
    # enormous integers reduced mod p. Its degree is a rigorous lower bound,
    # not a probabilistic degree assertion. Upper bounds are proved in REVIEW.md.
    prime=65521;require(sp.isprime(prime),'degree witness prime');rr,t=ring('t',GF(prime));values=[]
    for row in p['nodes']:
        op=row[0]
        if op=='variable':x=(VARS.index(row[1])+1)*t
        elif op=='integer':x=rr(row[1])
        elif op=='coefficient':x=rr(ports[row[1]]%prime)
        else:
            a,b=values[row[1]],values[row[2]];x=a+b if op=='add' else a-b if op=='sub' else a*b
        values.append(x)
    value=values[p['output']];want=NAMES[p['name']][0]
    require(value.degree()==want,'actual literal degree witness '+p['name'])
    require(p['exact_degree']==want,'declared exact degree')
    return {'upper_bound_certificate':degree_upper_bound(p),'prime':prime,'coordinate_map':{name:i+1 for i,name in enumerate(VARS)},'exact_specialized_degree':value.degree(),'nonzero_top_coefficient_mod_prime':int(value.LC),'upper_bound_reference':'REVIEW.md, Exact degree upper bounds','actual_coefficient_residues':{k:v%prime for k,v in ports.items()}}

def pellpow(A,n,mod=None):
    D=A*A-1;x,y=1,0;u,v=A,1
    while n:
        if n&1:x,y=x*u+D*y*v,x*v+y*u
        u,v=u*u+D*v*v,2*u*v
        if mod:x%=mod;y%=mod;u%=mod;v%=mod
        n//=2
    return x,y

def interpolation_controls():
    A,R,c=2,3,15;D=A*A-1;rows=[];old_period_fail=False
    for N in [1,2,3]:
        f,I=1,0;n=0
        while True:
            f,I=A*f+D*I,f+A*I;n+=1
            if n%2==0 and I%(4*N*c*c)==0:break
            require(n<5000,'bounded control construction')
        lam=4*n*f;g=math.gcd(lam,4*I*I)
        require((4*I)%g==0,'fixed strong pair CRT compatibility')
        require(pellpow(A,lam,f*f)==(1,0),'squared modulus Pell period')
        if pellpow(A,4*n,f*f)!=(1,0):old_period_fail=True
        details=[]
        for residue in [0,1,-1,2,7]:
            mod=4*I*I//g;rhs=(-4*I*residue)//g
            t=(rhs*pow(lam//g,-1,mod))%mod;index=R+lam*t
            require(index%4==3 and (index-R)%lam==0 and (index-R+4*I*residue)%(4*I*I)==0,'exact CRT index')
            S0=D*I;M=4*I*I*f*f
            chi,psi=pellpow(S0,index,M*S0)
            require(chi%S0==0,'odd quotient integrality')
            V=chi//S0
            require((V+c)%(f*f)==0 and (V+index)%(4*I*I)==0,'quotient congruences')
            numerator=(V+c-f*f*(c-R))%M
            require(numerator%(4*I*f*f)==0,'auxiliary T integrality')
            T=numerator//(4*I*f*f)
            require((T-residue)%I==0,'same strong pair realizes prescribed T class')
            details.append(residue)
        rows.append({'A':A,'R':R,'c':c,'N':N,'strong_index':n,'I_bits':I.bit_length(),'f_bits':f.bit_length(),'residues_tested':details})
    require(old_period_fail,'control rejects unsquared 4n period')
    return rows

def negative_controls(p):
    results=[]
    for mode in ['bad_gate','dead_node','bad_operation_count']:
        q=copy.deepcopy(p)
        if mode=='bad_gate':
            q['nodes'][q['output']][0]='add'
        elif mode=='dead_node':q['nodes'].append(['integer',98765])
        else:q['operations']+=1
        try:
            if mode=='bad_gate':exact_bindings(q)
            else:topology(q)
        except ValueError:results.append(mode)
        else:raise ValueError('failed negative control '+mode)
    omitted=[]
    for kind in ['A','Dm']:
        found=None
        for A in range(2,32,2):
            for c in range(1,20):
                D=A*A-1;Dm=1+D*c*c;I=2*c*c*(Dm if kind=='A' else A);Df=1+D*I*I
                g=math.gcd(Df,A*A*Dm)
                if g>1:found={'omitted_factor':kind,'A':A,'c':c,'I':I,'gcd':g};break
            if found:break
        require(found is not None,'nontrivial coprimality control '+kind);omitted.append(found)
    return {'mutated_packets_rejected':results,'coprimality_factor_omission_examples':omitted,'same_valuation_radical_warning':'sqrt(3)-sqrt(3)=0 although neither radicand is square; distinct valuations are essential.'}

def source_pins():
    pinpath=SRC/'SOURCE_PINS.json'
    if not pinpath.exists():pinpath=SRC/'source/SOURCE_PINS.json'
    pins=json.loads(pinpath.read_text());checked=[]
    for path,entry in pins['dependencies'].items():
        raw=(SRC/path).read_bytes();require(digest(raw)==entry['sha256'] and len(raw)==entry['bytes'],'retained source '+path);checked.append(path)
    require(all((SRC/x).is_file() for x in ['source/PROOF.md','source/centered11-proof.md','source/signed-quadratic-proof.md','source/PRIME_TWELVE.md']),'named theorem dependencies retained')
    return {'count':len(checked),'pin_file':str(pinpath.relative_to(SRC)),'all_pins_authenticated':True}

def main():
    vals,cert=coefficients();report={'status':'PASS','scope':'Independent finite audit and ordinary proof review; not a formal proof certificate.','sources':source_pins(),'actual_numerals':cert,'independent_finite_numeral_reconstruction':True,'identities':algebra(),'equations':[]}
    for name,(degree,ops) in NAMES.items():
        p=json.loads((SRC/(name+'.json')).read_text());counts=topology(p);require(p['operations']==ops,'independent expected gate count');bindings=exact_bindings(p);witness=degree_witness(p,vals)
        report['equations'].append({'name':name,'operations':ops,'counts':counts,'bound_registers':bindings,'degree_certificate':witness})
    report['negative_controls']=negative_controls(json.loads((SRC/'pair_fused11_rational.json').read_text()))
    report['fixed_witness_interpolation_modular_controls']=interpolation_controls()
    report['input_hashes']={name:digest((SRC/name).read_bytes()) for name in ['PROOF.md','section.tex']+[n+'.json' for n in NAMES]}
    out=OUT/('INDEPENDENT_CHECK.json' if __debug__ else 'INDEPENDENT_CHECK_OPTIMIZED.json');out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','equations':[{'name':x['name'],'degree':x['degree_certificate']['exact_specialized_degree'],'ops':x['operations']} for x in report['equations']],'output':out.name},indent=2))
if __name__=='__main__':main()
