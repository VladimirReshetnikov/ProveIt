#!/usr/bin/env python3
"""Independent whole formula, signed recovery and witness-map peer controls."""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import zipfile

ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'candidates/constructive-integer14-quadratic'
PARENT=ROOT/'candidates/constructive-integer14-shared'
FORMULAS=[('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('W','12*w+4'),('X','q*W'),('Y','q*v'),
 ('E','X*Y'),('a','E+Y'),('H','4*a+3'),('Delta','a*a+H'),
 ('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
 ('k','R+1+h*E'),('eta','c-Y*k'),('zeta','k-eta'),('i','2*r+1'),('I','i*c*c'),
 ('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),
 ('V','Df*(c*T-R)-c'),('Cy','Q*V*V-1'),('ell','X*Y*Y'),
 ('Dtau','1+ell*(ell+1)*k*k'),('K','X*(X+2*a*c)-1'),
 ('coneU','cone_A*F'),('coneZ','cone_B*C'),('G','coneU*coneZ-(q-coneU-coneZ)*(q-coneU-coneZ)'),
 ('Peta','eta*zeta'),('Gv','v*v*G'),('err','t*t-Gv-Peta+1'),('Pair','Gv*Peta-err*err'),
 ('B','(((Pair-1)-p1*p1)-p2*p2)-p3*(p3+1)'),('S','B*B'),
 ('M','2*q*q'),('U','M*H'),('Z','U*(n+V)+M*K+H*(v-q*q)'),
 ('s','delta*Z*Z'),('u','delta*U*U*Df'),('troot','delta*U*U*Dtau'),('yroot','U*U*Cy'),
 ('p','s+yroot-(u+troot)'),('pe','p*p-4*(s*yroot+u*troot)'),
 ('N','pe*pe-64*(s*yroot)*(u*troot)'),('output','N+S+N*S')]


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def module(n,p):
    spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def literal(packet,Terms):
    t=Terms();env={v:t.symbol(v)for v in packet['variables']}
    for v in ['beta','K0','MC','MF','cone_A','cone_B']:env[v]=t.symbol(v)
    expected=dict(env)
    for v,e in FORMULAS:expected[v]=t.expression(e,expected)
    values=[];counts=Counter()
    for i,node in enumerate(packet['nodes']):
        op=node[0]
        if op=='integer':values.append(t.integer(node[1]))
        elif op in ['variable','coefficient']:values.append(env[node[1]])
        else:
            need(op in ['mul','add','sub']and all(type(j)is int and 0<=j<i for j in node[1:]),'literal topology')
            values.append(t.operation({'mul':'*','add':'+','sub':'-'}[op],values[node[1]],values[node[2]]));counts[op]+=1
    need(values[packet['output']]==expected['output'],'entire independently transcribed formula identity')
    live=set();todo=[packet['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if packet['nodes'][i][0]in['mul','add','sub']:todo.extend(packet['nodes'][i][1:])
    need(live==set(range(len(values))),'every node and leaf live')
    need(counts==Counter(mul=70,add=26,sub=25)and sum(counts.values())==121,'actual121 live operations')
    nindex=next(i for i,r in enumerate(packet['nodes'])if r==['variable','n'])
    uses=[i for i,r in enumerate(packet['nodes'])if r[0]in ['mul','add','sub']and nindex in r[1:]]
    need(len(uses)==1 and packet['nodes'][uses[0]][0]=='add','n enters only the center')
    return dict(variables=14,operations=121,multiplications=70,additions=26,subtractions=25,
                all148_nodes_live=True,complete_universal_formula_identity=True,n_only_enters_center=True)


def pell(a,n):
    x,y=1,0
    for _ in range(abs(n)):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y if n>=0 else-y


def controls():
    recoveries=products=heights=maps=0;branches=set()
    for A in [-8,-5,-3,3,5,8]:
        B=abs(A);D=B*B-1
        for m in range(3,9):
            f,I=pell(B,m);S=D*I;need(f>2*I,'strong absolute gap')
            for nu in range(1,18,2):
                numerator,y=pell(S,nu);need(numerator%S==0,'odd auxiliary classification')
                for signV in [-1,1]:
                    V=signV*(numerator//S);r=(-V)%f
                    for c in [r,r-f]:
                        if not 30<abs(c)<=I:continue
                        need(S*S*V*V-(S*S-1)*y*y==1,'signed auxiliary norm')
                        need(any(pell(B,p)[1]==abs(c)for p in range(1,m+1)),'signed main recovery')
                        branches.add((1 if A>0 else-1,1 if c>0 else-1,signV));recoveries+=1
        H=4*A-5;a=A-2
        for R in range(1,26,2):
            d0,c0=pell(A,R);e=2**R
            need(c0==pell(B,R)[1],'odd-index psi A-sign transfer')
            for sigma in [-1,1]:
                c=sigma*c0;d=sigma*d0
                for X in [-e-1,-e,-1,1,e,e+1]:
                    K=X*(X+2*a*c)-1;z=sigma*X
                    need((e*K-(z-e)*(e*z+1))%abs(H)==0,'signed entire quadratic product congruence')
                    need(e*z+1!=0 and(e*z+1)%2==1,'odd second factor for both signs')
                    products+=1
                # Both unrestricted center maps, at either H sign and either c sign.
                X=sigma*e;K=X*(X+2*a*c)-1;b0=X+a*c
                need(K%H==0 and(d-b0)%H==0,'integral quadratic and restored-main projections')
                for n,V,M,l in [(-9,-4,2,3),(0,5,18,-2),(7,-3,50,0)]:
                    gamma=(d-b0)//H;nold=n+K//H+gamma
                    new=Fraction(n+V)+Fraction(K,H)+l
                    old=Fraction(nold+V)+Fraction(b0,H)+l
                    need(old==new+Fraction(d,H),'exact new-to-old center map')
                    # Choose arbitrary integral three-root targets; positivity of n is irrelevant.
                    f,tau,y=11,13,17;nnew=f+tau+y-V-K//H-l
                    need(Fraction(nnew+V)+Fraction(K,H)+l==f+tau+y,'exact old-to-new center map')
                    maps+=1
    need(len(branches)==8,'all eight A/c/V sign branches covered')
    for x in [64,65,97,128,1024]:
        for r in [10,11,24,25,49]:
            D=(x-3)**r;m=D//2;H=4*(x-1)*m-3
            need(2*m>D-2 and H>3*x*m>x*D>2**(4*r+4)*x*x,'minimal signed whole-product bound')
            heights+=1
    return dict(main_recovery_weak_bound_cases=recoveries,all_eight_A_c_V_sign_branches=sorted(map(list,branches)),
                signed_product_cases=products,strict_height_cases=heights,unrestricted_center_maps=maps)


def distinguished():
    # Exact monomial accounting after selecting all twelve h*a terms from
    # k0^12 and all four q0^4*z terms from R0^4 in the proven top form.
    def product(*items):
        out=Counter()
        for item in items:out.update(item)
        return out
    def power(x,n):return Counter({k:v*n for k,v in x.items()})
    q=Counter(two=1,three=1,beta=1,j=1);W=Counter(two=2,three=1,w=1)
    X=product(q,W);Y=product(q,Counter(v=1));a=product(X,Y);i=Counter(two=1,r=1)
    result=product(Counter(two=28),power(a,44),power(i,16),Counter(c=32),power(q,32),power(X,4),power(Y,16),Counter(h=12,z=4))
    # The compressed a^44*... form already includes the selected k/R terms.
    # It is equivalent to2^28*a^32*i^16*c^32*q^16*R^4*X^4*Y^16*k^12.
    want=dict(two=280,three=188,beta=140,j=140,w=48,v=60,h=12,r=16,c=32,z=4)
    need(dict(result)==want,'exact distinguished coefficient and exponents')
    need(sum(v for k,v in result.items()if k not in ['two','three','beta'])==312,'distinguished total degree312')
    return dict(coefficient='2^280*3^188*beta^140',exponents={k:v for k,v in result.items()if k not in ['two','three','beta']})


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    helper=ROOT/'reviews/quadratic10-page-peer.py';Terms=module('independent_prior_peer_AC_terms',helper).Terms
    packet=json.loads((HERE/'equation.json').read_text());binding=json.loads((HERE/'coefficients/BINDING.json').read_text())
    report=literal(packet,Terms);ports={}
    for n,pin in binding['payloads'].items():
        p=HERE/'coefficients'/pin['file'];raw=gzip.decompress(p.read_bytes())
        need(p.read_bytes()==(PARENT/'coefficients'/pin['file']).read_bytes(),'all original six payload bytes unchanged')
        need(digest(raw)==pin['raw_sha256']and len(raw)==pin['raw_bytes'],'entire raw fixed integer')
        ports[n]=dict(raw_sha256=digest(raw),bits=int.from_bytes(raw,'little').bit_length())
    mutations=[]
    for label,target in [('K constant polarity','K'),('norm polarity','N')]:
        bad=deepcopy(packet);idx=packet['named_registers'][target];bad['nodes'][idx][0]='add'
        try:literal(bad,Terms)
        except ValueError:mutations.append(label)
        else:raise ValueError('false semantic mutation accepted')
    archive=ROOT.parents[1]/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
    need(digest(archive.read_bytes())=='37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0','original complete ZIP')
    with zipfile.ZipFile(archive)as z:
        prefix=z.read('ConZFC_Constructive_Reductions_2026-10-23/integer14/upstream/provenance/RESIDUE_AND_DETERMINANT.md')
        need(prefix==(HERE/'source/RESIDUE_AND_DETERMINANT.md').read_bytes(),'exact borrowed source before gamma projection')
    replays={}
    for op in ['check','build']:
        for mode in ['normal','optimized']:
            p=Path('/tmp/proofs62ff-signed14-peer-'+op+'-'+mode+'.json');data=json.loads(p.read_text());need(data['status']=='PASS','fresh replay PASS')
            if op=='build':need(data['check']is True,'exact full byte rebuild check')
            else:need(data['optimized_python']==(mode=='optimized'),'correct check mode')
            replays[op+'_'+mode]=dict(path=str(p),sha256=digest(p.read_bytes()),result=data)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal=report,
                independently_rejected_mutations=mutations,supplementary_signed_controls=controls(),
                exact_distinguished_monomial=distinguished(),whole_six_original_ports=ports,
                equation_sha256=digest((HERE/'equation.json').read_bytes()),ordinary_proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
                borrowed_source_sha256=digest(prefix),independent_terms_helper_sha256=digest(helper.read_bytes()),
                fresh_replays=replays,
                scope='Independent adversarial ordinary proof plus complete universal formula/DAG binding, authentic six-port transfer and fresh normal/O literal checks/rebuilds. No pointwise parent identity or new native/internalZFC proof; no Lean.')
    s=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(s)
    print(s,end='')


if __name__=='__main__':main()
