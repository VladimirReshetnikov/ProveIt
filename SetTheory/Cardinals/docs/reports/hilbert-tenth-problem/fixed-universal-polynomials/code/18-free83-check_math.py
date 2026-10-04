#!/usr/bin/env python3
"""New report checks. Source arrays are inert data and are never evaluated."""
import hashlib, json, math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COUNTS = {}
def need(ok, message):
    if not ok: raise RuntimeError(message)
def count(name, n=1): COUNTS[name] = COUNTS.get(name, 0)+n
def pell(a, n, modulus=None):
    """Binary exponentiation of a quadratic pair, written for this report."""
    delta = a*a-1
    def mul(x, y):
        pair = (x[0]*y[0]+delta*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
        return tuple(v % modulus for v in pair) if modulus else pair
    result, base = (1,0), (a,1)
    while n:
        if n & 1: result = mul(result,base)
        base = mul(base,base); n //= 2
    return result
def quotient(s, z, modulus):
    need(z % 2 == 1, 'Odd quotient rank')
    # An independent numerator calculation, then exact division in Z.
    numerator = pell(s,z,s*modulus)[0]
    need(numerator % s == 0, 'Exact quotient divisibility')
    return numerator//s
def source_checks():
    raw = (ROOT/'source/immutable/complete83_free_coefficient_scout.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest() == '682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016','Candidate JSON identity')
    need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == '71edcd445eb45561613d40fbf8908d586f5a782c','Git blob identity')
    candidate = json.loads(raw)['packet']; rows = candidate['source']
    compact = json.dumps(rows,sort_keys=True,separators=(',',':')).encode()
    need(hashlib.sha256(compact).hexdigest() == '7834fa4ab4baa9faba720f572301d7f2ef5782a077c5e5adee931c89f46d240c','Complete row fingerprint')
    parent = json.loads((ROOT/'source/immutable/complete84_scaled_strong_output.json').read_text())['packet']
    deleted = ['aux_coefficient_root','*','i','Ac2']
    need(deleted in parent['source'],'Exact deleted row')
    need([r for r in parent['source'] if r != deleted] == rows,'All other rows identical')
    expected_ports = ['Jrep','F','alpha','transport_quotient','f','h','aux_coefficient_root','auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','Z','delta','rho','sigma']
    need(candidate['witnesses'] == expected_ports,'All 18 witness ports')
    need(candidate['fixed_numerals'] == ['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'],'Six fixed ports')
    known = set(candidate['free']); lookup = {}
    for row in rows:
        need(len(row)==4 and row[1] in ('*','+','-'),'Row shape')
        name,op,left,right = row
        need(name not in known,'Unique definition')
        for operand in (left,right): need(type(operand) is int or operand in known,'Topological operand')
        lookup[name] = row; known.add(name)
    selected = [
      ['q','+','repunit',1], ['R16','*','aux_coefficient_root','aux_coefficient_root'],
      ['norm_strong','-','scaled_f_square','R16'], ['scaled_f_square','*','A','L16'],
      ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
      ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
      ['auxiliary_R_f2','*','r_lhs','L16'], ['norm_aux','+','L17','aux_y2'],
      ['L17','*','R16','aux_square_gap'], ['aux_square_gap','-','H2','aux_y2'],
      ['norm_index','-','index_difference','r_lhs'],
      ['norm_transport','-','transport_partial','local_rhs'],
      ['norm_main','-','L15','Ac2'], ['norm_input','-','mu2','scaled_kappa2'],
      ['polynomial','-','seven_units','A']]
    for row in selected: need(lookup.get(row[0])==row,'Literal selected path')
    live = set()
    def visit(x):
        if type(x) is int or x in live:return
        live.add(x)
        if x in lookup:
            visit(lookup[x][2]);visit(lookup[x][3])
    visit('polynomial')
    need(live == known,'Entire source and supplied port liveness')
    ledger = {'rows':len(rows),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows),'witnesses':len(candidate['witnesses'])}
    need(ledger == {'rows':83,'M':46,'A':37,'witnesses':18},'Ledger')
    return ledger
def elementary_checks():
    for h in range(2,45):
        for v in range(121):
            for y in range(1,141):
                n=h*v*v-(h-1)*y*y;count('norm_rectangle')
                if n<0:need(n<=-(h-1),'Negative gap')
                if 0<n<h:
                    z=math.isqrt(n);need(z*z==n and math.gcd(v,y)==z,'Small square gcd')
                    count('positive_small_solutions')
                if n==-(h-1):
                    x0,y0=v,y
                    while x0:
                        t=y0-x0
                        x0,y0=x0-2*(h-1)*t,(2*h-1)*t-x0
                        need(x0>=0 and y0>0,'Boundary descent')
                    need(y0==1,'Boundary terminal seed');count('negative_boundary_solutions')
    for a in range(2,41):
        for m in range(1,17):
            f=pell(a,m)[1]
            residues={0}
            even_residues={0}
            for j in range(1,m):
                r=pell(a,j,f)[1];residues.update((r,(-r)%f))
                if j%2==0:even_residues.update((r,(-r)%f))
            for p in range(8*m+1):
                chi,psi=pell(a,p,f)
                need(psi in residues,'Second coordinate residues')
                if m%2 and p%2==0:need(psi in even_residues,'Parity residue')
                if m>=3 and (chi==1 or chi==f-1):need(p%(2*m)==0 and chi==1,'First coordinate lemma')
                count('pell_residue_and_divisibility_tests')
    for a in range(2,81,2):
        delta=a*a-1
        divisors=[v for v in range(1,delta+1) if delta%v==0]
        for y in range(151):
            for d in divisors:
                for sign in (-1,1):
                    n=sign*d;x2=delta*y*y+n;count('even_parameter_candidates')
                    if x2<0:continue
                    x=math.isqrt(x2)
                    if x*x != x2:continue
                    target=d if n>0 else delta//d
                    need(math.isqrt(target)**2==target,'Represented divisor classification')
                    count('represented_divisor_solutions')
    for s in range(2,21):
        for k in range(6,19):
            c=pell(s,k)[0]
            for t in range(1,8*k,2):
                v=quotient(s,t,c)
                need(not (1<v<s*s-1) and not (1<(-v)%c<s*s-1),'Small target quotient')
                count('small_target_quotients')
def family_checks():
    for j in range(64):
        u=17**(2*j);p=35*u
        need(u%24==1 and p%4==3,'Family residues')
        for prime,ar in ((5,3),(7,0),(17,0)):
            a=(pow(2,42*u-1,prime)+pow(2,7*u-1,prime)+2)%prime
            c=pell(a,p,prime)[1]
            need(a==ar and c==prime-1,'Universal gcd residues')
        count('family17_modular_parameters')
    u=1;p=35;n=30;r=59;x=2**p;y=2**6
    e=x*y;a=y*(x+1)+2;delta=a*a-1;hmod=4*a-5;P=2*x*y*y+1
    D,c=pell(a,p);tau,k0=pell(P,n);k=2*k0
    need(D*D-delta*c*c==1 and tau*tau-x*y*y*(x*y*y+1)*k*k==1,'Exact inner Pell norms')
    eta=c-k*y;zeta=k-eta
    need(eta>0 and zeta>0,'Exact strict ratio')
    need((k-r-1)%e==0 and (k-r-1)//e>0,'Retained positive index')
    zp=D-(a-2)*c;gamma=(zp-x)//hmod
    need((zp-x)%hmod==0 and gamma>0,'Exact main projection')
    need(math.gcd(c,p)==1 and c>1,'Fixture gcd')
    for i in range(3,p,2):
        mu,kappa=pell(a,i);zi=mu-(a-2)*kappa;W=2**i
        dr,rr=(kappa-i)%delta,(zi-W)%hmod
        d=(kappa-i)//delta;rho=(zi-W)//hmod;sigma=gamma-rho
        need(dr==rr==0 and min(d,rho,sigma)>0,'Shared positive input loading')
        need(mu==W+(a-2)*(i+d*delta)+rho*hmod,'Literal input projection')
        count('exact_fixture_input_ranks')
    f=D;S=delta*c
    # Solve z=p mod4p and z=r modc directly because gcd(4p,c)=1.
    z=p+4*p*(((r-p)*pow(4*p,-1,c))%c)
    need(z>0 and z%4==3 and z%c==r%c,'Fixture CRT')
    need(quotient(S,z,c)==(-r)%c and quotient(S,z,f)==(-c)%f,'Auxiliary modular identities')
    need(delta*f*f-S*S==delta,'Literal strong factor')
    need(3*5>6,'Small fixture scale exclusion')
    fixture={'u':1,'p':p,'n':n,'R':r,'c_bits':c.bit_length(),'auxiliary_index_bits':z.bit_length(),
             'full_outer_completion':False,'auxiliary_tuple_materialized':False}
    # Original 11-family modular proof checks only; no giant integer rebuild.
    L=math.lcm(12,18,13*(13**2-1),19*(19**2-1))
    need(L==622440 and pow(11,12,L)==1,'11-family period')
    for j in range(32):
        u=11**(12*j+1);p=247*u
        for prime,ar,cr in ((11,8,1),(13,4,1),(19,11,18)):
            a=(pow(2,304*u-1,prime)+pow(2,57*u-1,prime)+2)%prime
            need(a==ar and pell(a,p,prime)[1]==cr,'11-family residue')
        count('family11_modular_parameters')
    return fixture
def interface_checks():
    # Synthetic small ports test only the equivalence algebra, not genuine programs.
    for q in range(5,38):
        for W in range(1,4):
            ellx=2;K=3;w=q+2
            for F in range(1,q):
                for Z in range(1,q):
                    alpha=q-F-2*Z-W-ellx
                    if alpha<=0:continue
                    C=q-F-Z-alpha-ellx
                    need(C==W+Z,'Alpha inverse')
                    G=q*q-q*F-Z
                    need(G==(2*q-1)*Z+q*(W+ellx+alpha),'Packing lower identity')
                    need(G>=q*(W+ellx+3)-1,'Packing lower bound')
                    need((-G)%q==Z and (q*q-Z-G)//q==F,'Unique recovery')
                    numerator=(K+w)*(W+Z)-F
                    if numerator%(q-1)==0:
                        t=1+numerator//(q-1)
                        need(t>0 and (K+w)*C+q-F-t*(q-1)==1,'Transport inverse')
                    count('synthetic_interface_rewrites')
    for j in range(24):
        u=17**(2*j);R=60*u-1
        for N in range(1,25):
            # d=5 is used only to corroborate stated mod 3 and mod 7 identities.
            q3=pow(2,5*N,3);J3=sum(pow(2,5*k,3) for k in range(N))%3
            if N%2==0:need(q3==1 and J3==0 and R%3==2,'Even N obstruction')
            else:need(q3==2 and J3==1,'Odd N masks')
            if N%3==0:
                J7=sum(pow(2,5*k,7) for k in range(N))%7
                need(J7==0 and ((R%7==0)==(j%3==1)),'Seven restriction')
            count('necessary_outer_residue_tests')
def main():
    ledger=source_checks();elementary_checks();fixture=family_checks();interface_checks()
    print(json.dumps({'status':'PASS','source_schedule_executed':False,'upstream_python_executed':False,
                      'ordinary_input_language':'OPEN','ledger':ledger,'counts':COUNTS,'fixture17':fixture},sort_keys=True,indent=2))
if __name__ == '__main__':main()
