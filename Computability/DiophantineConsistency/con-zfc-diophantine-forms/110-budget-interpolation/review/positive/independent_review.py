#!/usr/bin/env python3
"""Independent review of the ten-positive 912/126 packet.

Uses SymPy 1.14.0 for exact polynomial arithmetic. Imports no packet code.
Run both normally and with -O. Finite checks do not replace the unbounded
mathematical review in REVIEW.md or the inherited compiler calibration.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from itertools import product
import gzip, hashlib, json, sys, time
import sympy as S

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1] / 'positive' / 'ten_centered'

def require(ok, why):
    if not ok:
        raise ValueError(why)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def expected_cuts():
    # Independent transcription of the printed formulas, including the
    # intermediate power registers needed to compare local arithmetic cuts.
    raw = '''
J = 3*j+1
q_minus_1 = beta*J
q = q_minus_1+1
q2 = q*q
q3 = q2*q
q4 = q2*q2
U = q4*q
h = F+alpha
C = q-h
Y = q3*s
E = X*Y
k = eta+zeta
kY = k*Y
c = kY+eta
c2 = c*c
a = E+Y
H = 4*a+3
Delta = a*a+H
ell = E*kY
R = (q_minus_1*(q-F)+alpha)*(q2-1)+(MC+q*MF)*J
Bt = (q*K0+X)*C-q*F
I = i*c2
I2 = I*I
Df_minus_1 = Delta*I2
Df = 1+Df_minus_1
Q = Delta*Df_minus_1
delta = Q-1
Told = T+h
Cf = (a+2)*I
cT = c*Told
V = Df*(cT-R)-c
Dt = ell*(ell+k)+1
Dd = 1+Delta*c2
L = k*Told
W = 1+q_minus_1*L
v = k-R-1
b0 = X+a*c
M = q_minus_1*U
center = ell+k+n+L+s+V+Cf
Z = M*(H*center+b0)-H*U*W*Bt+H*q_minus_1*(q4*X-v)
M2 = M*M
M2H2 = M2*H*H
A = M2H2*Dt
B = M2H2*Df
D = M2*Dd
Cnum = M2H2*(Q*V*V-1)
sigma = A+B+D
AB = A*B
pairs = AB+(A+B)*D
prod = AB*D
Z2 = Z*Z
delta2 = delta*delta
delta3 = delta2*delta
delta_Z2 = delta*Z2
ahat = delta*(Z2-sigma)+Cnum
ahat2 = ahat*ahat
tz = delta*Cnum*Z2
khat = ahat2+4*(tz-delta2*pairs)
rhat = 16*delta3*prod
bhat = ahat*khat-rhat
ehat = khat*khat+16*tz*ahat2-4*rhat*(delta_Z2+Cnum)
P10 = ehat*ehat-64*tz*bhat*bhat
'''
    lines = [line.split('=',1) for line in raw.strip().splitlines()]
    allnames = set('j F alpha i T X s n eta zeta beta K0 MC MF'.split())
    allnames.update(name.strip() for name, expr in lines)
    syms = {name:S.Symbol(name) for name in allnames}
    return {name.strip():S.sympify(expr.strip(),locals=syms)
            for name, expr in lines}, syms

def operate(op, x, y):
    return x*y if op=='*' else x+y if op=='+' else x-y

def above_cuts(packet, target, cuts):
    rows = {name:(op,a,b) for name,op,a,b in packet['source']}
    cache = {}
    def rec(node):
        if isinstance(node,int): return S.Integer(node)
        if node in cuts: return S.Symbol(cuts[node])
        if node not in rows: return S.Symbol(node)
        if node not in cache:
            op,a,b=rows[node]
            cache[node]=S.expand(operate(op,rec(a),rec(b)))
        return cache[node]
    return rec(target)

def graph_check(packet):
    require(packet['variables']==['j','F','alpha','i','T','X','s','n','eta','zeta'], 'Variable domain changed')
    require(packet['fixed_numerals']==['beta','K0','MC','MF'], 'Fixed tuple changed')
    require(packet['domain']=='strictly positive integers','Wrong domain')
    avail=set(packet['variables']+packet['fixed_numerals']); needed={packet['output']}
    for name,op,a,b in packet['source']:
        require(name not in avail,'Duplicate register')
        require(op in '+-*','Nonbinary or uncharged operation')
        require(all(type(v) is int or v in avail for v in (a,b)), 'Forward reference')
        avail.add(name)
    for name,op,a,b in reversed(packet['source']):
        if name in needed: needed.update([a,b])
    require(all(name in needed for name,*_ in packet['source']), 'Dead gate')
    require(set(packet['variables']+packet['fixed_numerals'])<=needed, 'Unused input')
    count=Counter(row[1] for row in packet['source'])
    require(len(packet['source'])==126 and count==Counter({'*':75,'+':34,'-':17}), 'Wrong gate count')
    require(packet['operations']==126 and packet['operation_breakdown']==dict(count),'Wrong count metadata')
    return dict(count)

def cut_check(packet):
    expected,syms=expected_cuts(); named=packet['named_registers']
    require(set(named)==set(expected),'Missing cut')
    require(len(set(named.values()))==len(named),'Aliased cut')
    for name,wire in named.items():
        cuts={v:k for k,v in named.items() if k!=name}
        got=above_cuts(packet,wire,cuts)
        require(S.expand(got-expected[name])==0,'Wrong cut: '+name)
    return len(named)

def norm_check(packet):
    # Multiply all sixteen linear factors directly in an independent
    # five-variable polynomial ring. No compact-norm formula is imported.
    z,*roots=S.symbols('Z r0 r1 r2 r3')
    gens=(z,*roots)
    f=S.Poly(1,*gens,domain=S.ZZ)
    for signs in product([-1,1],repeat=4):
        f *= S.Poly(z-sum(s*r for s,r in zip(signs,roots)),*gens,domain=S.ZZ)
    A,B,D,N,h=S.symbols('A B D Cnum delta')
    converted=0
    for exps, coeff in f.terms():
        ez,*er=exps
        require(all(v%2==0 for v in er),'Surviving radical')
        eA,eB,eD,eN=(v//2 for v in er)
        require(eN<=8,'Denominator exponent')
        converted += coeff*z**ez*A**eA*B**eB*D**eD*N**eN*h**(8-eN)
    reference=S.Poly(converted,z,A,B,D,N,h,domain=S.ZZ)
    named=packet['named_registers']
    cuts={named[name]:name for name in ('Z','A','B','D','Cnum','delta')}
    literal=S.Poly(above_cuts(packet,packet['output'],cuts),z,A,B,D,N,h,domain=S.ZZ)
    require(reference==literal,'Literal graph differs from sixteen-factor norm')
    require(len(f.terms())==495 and len(reference.terms())==495,'Unexpected norm term count')
    return reference

def leading_check():
    q,k,X,s,i,T,F,alpha=S.symbols('q k X s i T F alpha')
    Y=q**3*s; a=X*Y; c=k*Y; I=i*c*c
    V=a*a*I*I*c*(T+F+alpha)
    K=4*q**6*a; Cf=a*I; ell=X*k*Y*Y; Q=a**4*I*I
    # Sixteen formal factors have leading terms 2KV (8), 2KCf (4),
    # 2Kell (2), K I^2/(2Cf) (2); delta^8 contributes Q^8.
    got=S.cancel(Q**8*(2*K*V)**8*(2*K*Cf)**4*(2*K*ell)**2*(K*I**2/(2*Cf))**2)
    wanted=2**44*q**558*i**38*k**86*X**68*s**154*(T+F+alpha)**8
    require(S.expand(got-wanted)==0,'Wrong leading coefficient formula')
    require(8*49+4*27+2*21+2*17+8*42==912,'Wrong branch degree sum')
    # The three root defects establish the printed Laurent orders.
    aa,cc,ii,xx,DD,VV=S.symbols('a c I X Delta V')
    HH=4*aa+3; DD=aa*aa+HH
    require(S.expand(((aa+2)*ii)**2-(1+DD*ii*ii)-(ii*ii-1))==0,'Strong defect')
    require(S.expand(1+DD*cc*cc-(xx+aa*cc)**2-(HH*cc*cc-2*aa*cc*xx-xx*xx+1))==0,'Main defect')
    Qs,Vs=S.symbols('Q V')
    require(S.cancel((Qs*Vs**2-1)/(Qs-1)-Vs**2-(Vs**2-1)/(Qs-1))==0,'Auxiliary defect')
    return {'degree':912,'factor_degrees':{'49':8,'27':4,'21':2,'17':2},'leading_form_verified':True}

def coefficient_check():
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    upstream=json.loads((ROOT/'upstream/interfaces/compact44_BINDING.json').read_text())
    oldports={row['port']:row for row in upstream['materialization']['files']}
    rename={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}
    vals={}; result={}
    for name,row in binding['ports'].items():
        payload=(ROOT/'coefficients'/row['gzip_payload']).read_bytes(); raw=gzip.decompress(payload)
        require(sha(payload)==row['gzip_sha256'] and sha(raw)==row['sha256'], 'Payload hash '+name)
        old=oldports[rename[name]]
        require(all(row[key]==old[key] for key in ('bits','raw_bytes','sha256','gzip_sha256')), 'Native binding '+name)
        val=int.from_bytes(raw,'little'); vals[name]=val
        require(val.bit_length()==row['bits'] and len(raw)==row['raw_bytes'],'Payload size '+name)
        require(raw==val.to_bytes((val.bit_length()+7)//8,'little'),'Not minimal byte encoding')
        result[name]={'bits':val.bit_length(),'sha256':sha(raw)}
    require(vals['beta']==2**590069-1,'Wrong beta')
    require(vals['beta']%3==1 and vals['K0']>0 and 0<vals['MC']<vals['beta'] and vals['beta']<vals['MF']<2*vals['beta'],'Tuple inequalities')
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for row in pins['files']:
        require(sha((ROOT/row['local']).read_bytes())==row['sha256'], 'Source hash '+row['local'])
    tm=[]
    for line in (ROOT/'upstream/interfaces/k215.tm').read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,v,d,t=line.split()
        tm.append([int(q),int(b),int(v),{'L':-1,'R':1}[d],int(t)])
    transitions_path=ROOT/'upstream/interfaces/k215_transitions.json'
    stored=json.loads(transitions_path.read_text())['transitions']
    require(tm==stored and len(tm)==430,'Transition JSON not the pinned TM')
    # The retained binding hashes the historical full transition serialization.
    # This packet reconstructs a minimal JSON from the pinned TM; semantics were
    # checked above rather than pretending those unequal byte hashes agree.
    result['transition_provenance']={'tm_rows':len(tm),
        'supplied_json_sha256':sha(transitions_path.read_bytes()),
        'historical_json_sha256':upstream['transition_json_sha256'],
        'exact_transition_equality_to_pinned_TM':True}
    return result,len(pins['files']),vals

def degree_specializations(packet,constants):
    t=S.Symbol('lambda'); results=[]
    for p in (1000003,1000033):
      for slopes in ([1]*10,[2,3,5,7,11,13,17,19,23,29]):
        x=dict(zip(packet['variables'],slopes))
        values={name:S.Poly(slope*t,t,modulus=p) for name,slope in x.items()}
        values.update({name:S.Poly(value%p,t,modulus=p) for name,value in constants.items()})
        def val(ref):
            return S.Poly(ref,t,modulus=p) if type(ref) is int else values[ref]
        for name,op,a,b in packet['source']:
            values[name]=operate(op,val(a),val(b))
        f=values[packet['output']]
        expected=(pow(2,44,p)*pow(3*(constants['beta']%p)*x['j'],558,p)
                  *pow(x['i'],38,p)*pow(x['eta']+x['zeta'],86,p)
                  *pow(x['X'],68,p)*pow(x['s'],154,p)
                  *pow(x['T']+x['F']+x['alpha'],8,p))%p
        require(f.degree()==912 and int(f.LC())%p==expected and expected!=0,'Univariate graph degree or lead')
        results.append({'prime':p,'slopes':slopes,'degree':f.degree(),'leading_coefficient':expected})
    return results


def inequality_diagnostics():
    # Exact rational bounds: deliberately choose h much larger than q,
    # including C<=0. No native C>0 bound is used in this diagnostic.
    from fractions import Fraction
    cases=0
    for q in (16,17,32):
      for X in (1,2,16):
       for s in (1,3):
        Y=q**3*s; a=Y*(X+1); H=4*a+3; Delta=a*a+H
        for h in (2,q-1,q,q+1,10**9):
         for T in (1,2,9):
          # Only the consequence of the integral first/main Pell equations
          # is required: k>8XY^2. Choose eta=1, zeta=k-1.
          k=8*X*Y*Y+2; c=k*Y+1; I=c*c
          Df=1+Delta*I*I; delta=Delta*Delta*I*I-1
          Rhat=q**3*(q+h); L=k*(T+h)
          require(c*h>Rhat,'Translation does not dominate R')
          require(delta-(Delta-1)*Df==Delta*(I*I-1),'Wrong denominator inequality')
          require(Fraction(c*(T+2*h),Delta-1)<Fraction(L,2),'y-V bound failure')
          gamma_bound=Fraction(2*c,H)+Fraction(k,q**5)+Fraction(Rhat,q**5)
          require(gamma_bound<Fraction(L,2),'one-sided gamma bound failure')
          cases+=1
    return cases

def rejected_mutations(packet, reference):
    cases=[]
    # All mutations preserve literal operation count and graph liveness.
    # This prevents a metadata-only checker from accepting wrong arithmetic.
    for name,target,old,new,checker in [
      ('final kernel scalar 64 -> 63',None,64,63,'norm'),
      ('remove auxiliary translation in cT','cT','Told','T','cut'),
      ('remove h from weight L','L','Told','T','cut')]:
        bad=deepcopy(packet); found=False
        wire=bad['named_registers'].get(target)
        oldref=bad['named_registers'].get(old,old)
        newref=bad['named_registers'].get(new,new)
        for row in bad['source']:
            if (target is None or row[0]==wire) and oldref in row[2:]:
                row[row.index(oldref,2)]=newref;found=True;break
        require(found,'Mutation target missing '+name)
        graph_check(bad)
        try:
            norm_check(bad) if checker=='norm' else cut_check(bad)
        except ValueError:
            cases.append({'mutation':name,'rejected':True,'same_gate_count':True})
        else:raise ValueError('Mutation escaped: '+name)
    return cases

def main():
    start=time.monotonic()
    packet_path=ROOT/'generated/p10_positive.json'
    packet=json.loads(packet_path.read_text())
    count=graph_check(packet); cuts=cut_check(packet)
    norm=norm_check(packet); degree=leading_check()
    coefficients,pins,constants=coefficient_check()
    degree_replays=degree_specializations(packet,constants)
    inequalities=inequality_diagnostics()
    negatives=rejected_mutations(packet,norm)
    receipt={'status':'PASS','python_optimization':sys.flags.optimize,'sympy_version':S.__version__,
             'circuit_sha256':sha(packet_path.read_bytes()),'operations':126,'operation_breakdown':count,
             'exact_named_cut_identities':cuts,'full_conjugate_norm_terms':len(norm.terms()),
             'degree_certificate_algebra':degree,'independent_polynomial_degree_replays':degree_replays,
             'coefficient_payloads':coefficients,
             'pinned_source_files':pins,'literal_TM_matches_transition_JSON':True,
             'inequality_diagnostic_cases':inequalities,'negative_controls':negatives,
             'elapsed_seconds':round(time.monotonic()-start,3),
             'boundary':'Unbounded proof reviewed in REVIEW.md; native/compiler/ZFC calibration remains inherited.'}
    destination=HERE/('REVIEW_OPTIMIZED.json' if sys.flags.optimize else 'REVIEW_NORMAL.json')
    destination.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
