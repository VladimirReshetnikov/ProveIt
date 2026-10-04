#!/usr/bin/env python3
"""Reconstructed independent bounded checks; source is inert data only.

This is newly written recovery code, not authenticated by an earlier checker
hash. No upstream Python or saved arithmetic schedule is executed.
"""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
 'complete82_auxiliary_square_product_chart.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
 'complete82_auxiliary_square_product_chart.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
 'complete82_auxiliary_square_product_chart.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9',
}

def need(ok, reason):
    if not ok:
        raise RuntimeError(reason)

def pair(A,n):
    need(A>=2 and 0<=n<=200, 'bounded Pell fixture only')
    D=A*A-1
    x,y=1,0
    for _ in range(n):
        x,y=A*x+D*y,x+A*y
    return x,y

def crt(a,m,b,n):
    need(gcd(m,n)==1, 'CRT coprimality')
    # A bounded search through a small second modulus independently implements CRT.
    need(n<=7, 'bounded CRT search')
    for j in range(n):
        z=(a+j*m)%(m*n)
        if z%n==b%n:
            return z or m*n
    raise RuntimeError('CRT failed')

def source_checks(src):
    for name,h in PINS.items():
        need(hashlib.sha256((src/name).read_bytes()).hexdigest()==h, 'source pin '+name)
    packet=json.loads((src/'complete82_auxiliary_square_product_chart.json').read_text())['packet']
    need(len(packet['source'])==82 and len(packet['witnesses'])==18, 'source size')
    need(packet['ordinary_input']=='x', 'ordinary input')
    need(packet['fixed_numerals']==['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'], 'fixed ports')
    # Compare literal rows as data; never interpret or execute the schedule.
    rows={r[0]:r[1:] for r in packet['source']}
    expected={
      'R10b':['+','eta','zeta'], 'R10a':['+','ksn2','eta'],
      'marked_rhs':['-','C_after_alpha','scaled_t'], 'W':['-','marked_rhs','Z'],
      'odd_index':['+','scaled_t','inner_bits'], 'index_rhs':['+','odd_index','index_product'],
      'gamma_sum':['+','rho','sigma'], 'R14':['+','D1','gam'],
      'gap':['+','gap_product','q_minus_FZ'], 'r_lhs':['+','rproduct','mask'],
      'norm_index':['-','index_difference','r_lhs'],
      'norm_transport':['-','transport_partial','local_rhs'],
      'auxiliary_Tf_minus_one':['-','auxiliary_Tf',1],
      'aux_u_rhs':['-','auxiliary_c_Tf','auxiliary_R_f2'],
      'aux_coefficient_root':['*','i','Ac2'], 'R16':['*','aux_coefficient_root','aux_coefficient_root'],
      'norm_aux':['+','L17','aux_y2'], 'norm_strong':['-','scaled_f_square','R16'],
      'polynomial':['-','seven_units','A'],
    }
    for name,rhs in expected.items():
        need(rows[name]==rhs, 'literal source row '+name)
    return len(expected)

def residue_checks():
    minimum=12
    count=0
    for K in range(35):
        for q7 in (2,4):
            choices=[h for h in range(1,13)
                     if (1+2*(K+pow(2,5*h,5)))%5
                     and (1+q7*(K+pow(2,5*h,7)))%7]
            need(len(choices)>=6, 'six exponent classes')
            minimum=min(minimum,len(choices))
            e=9 if K%5==1 else 8
            need((1+2*(K+pow(2,e,5)))%5!=0, 'e8/e9 invertibility')
            count+=1
    need((13*625)**4<2**625, 'uniform size base')
    need(8*3<2**6 and 40*2<2**10, 'ratio threshold bases')
    return count,minimum

def outer_checks():
    count=0
    branch=[0,0,0]
    bits=0
    for d,t in ((5,625),(5,3125),(25,625)):
        B,q=1<<d,1<<t
        J=(q-1)//(B-1)
        Q=q*q-1
        need(J*(B-1)==q-1 and (t//d)%2==1, 'repunit')
        for K in range(1,36):
            for MC in (2,6,10):
                for MF0 in (4,12,20,28):
                    for x in (1,2):
                        ell,b=2*d,5
                        I=ell*x+b
                        W=1<<I
                        need(t>=4*max(I,K.bit_length(),61,16), 'fixture sizing')
                        need(0<MC<B-1 and MC%4==2 and 0<MF0<B-1, 'necessary mask tests')
                        MF=MF0+B-1
                        M=(MC+q*MF)*J
                        m3=(MC+2*MF)%3
                        need(M%3==m3 and M%4==2, 'mask residues')
                        if m3:
                            eps=1 if m3==2 else -1
                            e=9 if K%5==1 else 8
                            L=K+(1<<e)
                            Astar=Q*(q*q-q*(L*W+1-eps))+M
                            beta=Q*(1+q*L)
                            need(gcd(beta,t)==1, 'case A inverse')
                            target=(3*e*pow(2,-1,t)-eps)%t
                            zt=(Astar-target)*pow(beta,-1,t)%t
                            Z=crt(zt,t,1,4)
                            F=L*(W+Z)+1-eps
                        else:
                            eps=1
                            h0=next(h for h in range(1,13)
                                    if gcd(Q*(1+q*(K+(1<<(5*h)))),35)==1)
                            e=5*h0
                            L=K+(1<<e)
                            Astar=Q*(q*q-q*L*W)+M
                            beta=Q*(1+q*L)
                            T=t//5
                            zt=(Astar-(7*h0-1))*pow(beta,-1,T)%T
                            Z=crt(zt,T,1,4)
                            z7=(Astar+1)*pow(beta,-1,7)%7
                            Z=crt(Z,4*T,z7,7)
                            F=L*(W+Z)
                        alpha=q-F-2*Z-W-ell*x
                        G=q*q-q*F-Z
                        R=G*Q+M
                        need(R==Astar-beta*Z, 'actual affine R')
                        need(0<Z<=6*t and F>0 and alpha>0 and F+Z<q, 'positive outer witnesses')
                        need(q-F-Z-alpha-ell*x==W+Z, 'actual marked C')
                        need(2*q-1<=G<=q*q-q-1 and 0<M<(q-1)*(1+2*q), 'packing cuts')
                        need((2*q-1)*Q<R<q**4-q**3 and R>q**3>100*t, 'R interval')
                        need(R%4==3 and R%3==m3, 'R residues')
                        if m3:
                            need((R+eps)%6==0, 'integer u')
                            u=(R+eps)//6
                            p,n,yexp=4*u,3*u,2*u-1
                            need(u%2==(0 if eps==1 else 1), 'u sign parity')
                        else:
                            need((R+1)%28==0, 'integer v')
                            v=(R+1)//28
                            p,n,yexp=20*v,14*v,15*v-1
                        need(2*n==R+eps and p%t==e%t, 'rank/transport coupling')
                        need(p>I and p>t+e and yexp>=3*t, 'all scale thresholds')
                        need(p*(p-n)==(yexp+1)*(2*n-p), 'resonance exponents')
                        need(p%2==0 and R%2==1 and p!=R, 'wrong rank')
                        # Algebraic transport check, without materializing 2^p.
                        C=W+Z
                        need(L*C+q-F-(q-1)==eps, 'transport constant sign')
                        count+=1
                        branch[m3]+=1
                        bits=max(bits,R.bit_length())
    return count,branch,bits

def pell_checks():
    count=0
    aux_count=0
    for family,values in (('u',range(3,16)),('v',range(2,7))):
        for j in values:
            if family=='u':
                p,n,yexp=4*j,3*j,2*j-1
                eps=1 if j%2==0 else -1
                R=6*j-eps
            else:
                p,n,yexp=20*j,14*j,15*j-1
                eps=1
                R=28*j-1
            X,Y=1<<p,1<<yexp
            E=X*Y
            a=Y*(X+1)
            A=a+2
            Dlt=A*A-1
            H=4*a+3
            P=2*X*Y*Y+1
            D,c=pair(A,p)
            tau,halfk=pair(P,n)
            k=2*halfk
            need(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1, 'first norm')
            need(D*D-Dlt*c*c==1 and c%2==0, 'main norm/even c')
            eta,zeta=c-Y*k,(Y+1)*k-c
            need(eta>0 and zeta>0 and eta+zeta==k, 'positive ratio coordinates')
            need(eta*X<4*p*Y*k, 'quantitative ratio estimate')
            need((k-2*n)%E==0 and (k-2*n)//E>0, 'positive h')
            need(k-((k-2*n)//E)*E-R==eps, 'actual index sign')
            I=3
            mu,kappa=pair(A,I)
            need((kappa-I)%Dlt==0 and (kappa-I)//Dlt>0, 'positive delta')
            need((D-a*c-X)%H==0 and (mu-a*kappa-(1<<I))%H==0, 'shared projection integrality')
            gp=(D-a*c-X)//H
            rho=(mu-a*kappa-(1<<I))//H
            sigma=gp-rho
            need(rho>0 and sigma>0, 'same positive rho/sigma')
            need(mu==(1<<I)+a*kappa+rho*H and D==X+a*c+(rho+sigma)*H, 'actual root formulas')
            need(mu*mu-Dlt*kappa*kappa==1, 'input norm')
            if j<=4:
                S=Dlt*c*c
                Faux=Dlt*c**4+1
                chi,yaux=pair(S,R)
                need(chi%S==0, 'odd auxiliary quotient')
                V=chi//S
                need((V+R*Faux)%c==0, 'even-c auxiliary integrality')
                U=(V+R*Faux)//c+1
                need(U>0 and V==c*(U-1)-R*Faux, 'literal auxiliary V')
                Na=S*S*(V*V-yaux*yaux)+yaux*yaux
                Ns=Dlt*Faux-S*S
                need(Na==1 and Ns==Dlt, 'auxiliary/strong norms')
                need((c*D-1)**2<Faux<(c*D)**2, 'nonsquare coordinate')
                need(Dlt*((eps*eps)*Na*(Faux-Dlt*c**4)-1)==0, 'full factor identity')
                aux_count+=1
            count+=1
    return count,aux_count

def auxiliary_congruences():
    count=0
    for c in range(1,25):
        for D in (2,3,8):
            S=D*c*c
            for R in (3,7,11,15):
                chi,y=pair(S,R)
                need(chi%S==0 and (chi//S+R)%c==0, 'all-parity quotient congruence')
                count+=1
    return count

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source-root',type=Path,default=HERE.parent/'square-product82-counterfamily-recovered-20261004'/'source')
    args=ap.parse_args()
    rows=source_checks(args.source_root)
    rc,rm=residue_checks()
    oc,bc,ob=outer_checks()
    pc,ac=pell_checks()
    result={
      'status':'PASS: fresh reconstructed independent checker; proof in audit.md',
      'recovery_status':'New checker and receipt after workspace replacement; no old byte-identity claim',
      'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'source_pins':PINS,
      'literal_source_rows_checked':rows,
      'saved_source_schedules_executed':0,
      'upstream_python_executed':0,
      'exponent_choice_residue_cases':rc,
      'minimum_residue0_exponent_choices':rm,
      'outer_diagnostic_cases':oc,
      'outer_cases_by_m3':bc,
      'largest_outer_R_bit_length':ob,
      'exact_pell_subsystem_cases':pc,
      'exact_auxiliary_even_c_cases':ac,
      'all_parity_auxiliary_congruences':auxiliary_congruences(),
      'full_genuine_numeral_tuple_materialized':False,
      'scope':'Necessary-mask diagnostic slices and small exact Pell subsystems corroborate the separately proved general theorem; they are not genuine compiler counterexamples.'
    }
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
