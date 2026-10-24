#!/usr/bin/env python3
"""Independent105-gate direct zero-offset cuts, carrier and degree340 certificate.

Imports no candidate producer or historical emitter. The independent sparse
conjugate-product oracle is copied/authenticated from the accepted parent.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'candidates/ten-positive-direct-base'
ZERO=ROOT/'candidates/ten-positive-zero-offset'
PARENT_SHA='63367b3b3a8f7ca35af73677ecd1c518578e59a3627a1e9d7a43550a7d391f49'
ZERO_SHA='047ea8145ef52ab939322f2147c75272e7a182016be78a453fbdf2d3c2a6a493'


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_bytes())
def digest(data):return sha256(data).hexdigest()


def sealed(path):
    manifest=path/'MANIFEST.json';files=load(manifest)['files']
    need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p!=manifest}==set(files),'whole closed packet '+str(path))
    for n,h in files.items():need(digest((path/n).read_bytes())==h,'whole sealed member '+n)


def evaluate(rows,inputs,modulus=None):
    env=dict(inputs)
    for n,op,a,b in rows:
        a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
        value=a+b if op=='+'else a-b if op=='-'else a*b
        env[n]=value if modulus is None else value%modulus
    return env


def verify_cuts(parent,child,cuts):
    old,rows=parent['source'],child['source'];records=cuts['all_parent_rows']
    need(len(old)==107 and [r['parent_index']for r in records]==list(range(107)),'all107 parent definitions accounted')
    need(cuts['deleted_parent_indices']==[5,6,12]and cuts['changed_parent_indices']==[13]and cuts['moved_parent_indices']==[18],
         'only privateE/a/a2 deletion and existingmuY sharing/base cut')
    target=[]
    for rec in records:
        i=rec['parent_index'];need(rec['old_row']==old[i],'entire actual parent row')
        if i in[5,6,12]:
            want={5:['E','*','X','Y'],6:['a','+','E','Y'],12:['a2','+','a',2]}[i]
            need(old[i]==want and rec['status']=='deleted_private','only exact private products/offset deleted');continue
        j=rec['child_index'];target.append(j);want=['Am1','*','muY','Xp1']if i==13 else old[i]
        need(rec['new_row']==rows[j]==want and rec['status']==('replaced_base_operand'if i==13 else'moved_shared'if i==18 else'retained'),
             'all retained, moved and changed literal operands')
    need(cuts['inserted_child_rows']==[dict(child_index=10,new_row=['Xp1','+','X',1])]and rows[10]==['Xp1','+','X',1],
         'only inserted shared Xplus1 expression')
    need(sorted(target+[10])==list(range(105))and len(set(target))==104,'complete105 child coverage including insertedgate')
    need([i for i,r in enumerate(old)if'E'in r[2:]]==[6]and[i for i,r in enumerate(old)if'a'in r[2:]]==[12]
         and[i for i,r in enumerate(old)if'a2'in r[2:]]==[13],'entire private E/a/a2 consumer boundary')
    need(rows[11]==old[18]==['muY','*','mu','Y']and rows[12]==['Am1','*','muY','Xp1'],'topological sharedmuY before newbase')
    need(cuts['parent_norm_tail_start']==94 and cuts['child_norm_tail_start']==92 and rows[92:]==old[94:],'entire13-gate weighted norm tail unchanged')
    need(child['witnesses']==parent['witnesses']==['J','F','alpha','i','T','x','Y','n','eta','zeta']
         and child['fixed_numerals']==parent['fixed_numerals']and child['coefficient_binding']==parent['coefficient_binding'],
         'same complete ten inputs and coherent four ports')
    need(child['domain']=='strictly positive integers','positive domain preserved')
    need(set(child['register_degrees'])==set(parent['register_degrees'])-{'a'},'literal a removed; proof a remains an abbreviation only')


def topology(child):
    rows=child['source'];known=set(child['witnesses']+child['fixed_numerals'])
    degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']};deps={}
    for n,op,a,b in rows:
        need(n not in known and op in['+','-','*']and all(type(x)is int or x in known for x in[a,b]),'fresh acyclic ring gate')
        da,db=(0 if type(x)is int else degrees[x]for x in[a,b]);degrees[n]=da+db if op=='*'else max(da,db)
        deps[n]=[a,b];known.add(n)
    live=set();todo=[child['output']]
    while todo:
        v=todo.pop()
        if type(v)is int or v in live:continue
        live.add(v);todo.extend(deps.get(v,[]))
    need(live==known,'all105 gates,10 inputs and4 fixedports live')
    counts=dict(Counter(r[1]for r in rows));need(len(rows)==child['operations']==105 and counts==child['operation_breakdown']=={'*':63,'+':24,'-':18},'actual live105 operation census')
    need(degrees['N']==child['syntactic_degree']==384 and child['exact_degree']==340,'degree metadata before exact cancellation')
    for n,d in child['register_degrees'].items():need(degrees[n]==d,'actual register degree bound '+n)
    return degrees,counts


def verify_zero_cuts(zero,child,cut):
    old,rows=zero['source'],child['source'];records=cut['all_parent_rows']
    need([r['parent_index']for r in records]==list(range(99)),'all99 zero-offset parent rows accounted')
    changes={4:['X','+','q','x'],34:['qK0X','+','qK0','X'],35:['qK0XC','*','qK0X','C'],36:['B','-','qK0XC','qF'],
        54:['qm1L','*','qbJ','L'],56:['P1','*','q4','bJ'],68:['lowY','*','qbJ','Y'],69:['WBt','*','W','B'],71:['inner0','-','lowY','q3WBt']}
    inserted=[(34,34,'before',['qK0','*','q','K0']),(37,36,'before',['qF','*','q','F']),
        (56,54,'before',['qbJ','*','q','bJ']),(59,56,'before',['q4','*','q3','q']),
        (75,71,'before',['lowX','*','bJ','X']),(77,71,'after',['inner','-','inner0','lowX'])]
    need(cut['changed_parent_indices']==sorted(changes),'only exact primitive carrier/base cuts from99')
    need(cut['inserted_rows']==[dict(child_index=c,parent_index=p,position=s,row=r)for c,p,s,r in inserted],'six literal direct-carrier insertions')
    covered=[]
    for record in records:
        i,j=record['parent_index'],record['child_index'];covered.append(j)
        need(record['old_row']==old[i]and record['new_row']==rows[j]==changes.get(i,old[i]),'all sameX kernel rows/changed carrier operands bound')
        need(record['status']==('replaced_carrier_cut'if i in changes else'retained'),'complete99 row classification')
    for j,_,_,row in inserted:need(rows[j]==row,'actual inserted carrier row');covered.append(j)
    need(sorted(covered)==list(range(105)),'all105 rows covered exactlyonce by99 plus six')
    need(rows[92:]==old[86:]and cut['child_norm_tail_start']==92 and cut['parent_norm_tail_start']==86,'same complete norm tail as99')
    need(child['witnesses']==['x'if v=='w'else v for v in zero['witnesses']]
         and child['fixed_numerals']==zero['fixed_numerals']and child['coefficient_binding']==zero['coefficient_binding'],'complete sameX input and four-port map')


def scalar_spec(inputs):
    J,F,alpha,i,T,x,Y,n,eta,zeta=[inputs[v]for v in['J','F','alpha','i','T','x','Y','n','eta','zeta']]
    beta,K0,MC,MF=[inputs[v]for v in['beta','K0','MC','MF']]
    q=beta*J+1;mu=q*q+1;X=q+x;a=Y*(X+1);k=eta+zeta;c=k*Y+eta
    A=mu*a+1;D=A*A-1;H=4*A-5;I=i*c*c
    V0=X*mu*mu*Y*Y;Dtau=V0*(V0+1)*k*k+1
    R=((q-1)*(q-F)+alpha)*(q*q-1)+J*(MC+q*MF)
    C=q-F-alpha;B=(q*K0+X)*C-q*F;e=k-R-1;b=c*(T+alpha)-R
    Df=D*I*I+1;Q=D*D*I*I;delta=Q-1;V=Df*b-c;Dnum=Q*V*V-1
    W=1+q*(q-1)*(H*I+b);P1=q**4*(q-1);M=P1*mu*mu*H;Kpos=X*(3*c-2*X)+2
    Z=P1*mu*mu*(H*(n+V)+Kpos)+H*(mu*mu*(q*(q-1)*Y-q**3*W*B-(q-1)*X)-P1*e)
    fs=delta*Z*Z;fa=9*delta*M*M*Dtau;fb=delta*M*M*Df;fc=M*M*Dnum
    N=((fs+fc-fa-fb)**2-4*(fs*fc+fa*fb))**2-64*fs*fc*fa*fb
    return dict(q=q,mu=mu,X=X,c=c,Am1=A-1,Dp=D,Hp=H,I=I,Dtau=Dtau,R=R,
        B=B,Df=Df,Q=Q,delta=delta,V=V,Dnum=Dnum,W=W,Mtot=M,Kpos=Kpos,Znum=Z,fs=fs,fa=fa,fb=fb,fc=fc,N=N)


def line_degree(values,modulus):
    degree=-1;level=0
    while values:
        if values[0]:degree=level
        values=[(b-a)%modulus for a,b in zip(values,values[1:])];level+=1
    return degree


def pell(a,h):
    x,y=1,0
    for _ in range(h):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def main():
    if(HERE/'MANIFEST.json').exists():sealed(HERE)
    sealed(PARENT);sealed(ZERO)
    raw=(HERE/'source/direct/equation.json').read_bytes();zero_raw=(HERE/'source/zero/equation.json').read_bytes()
    need(digest(raw)==PARENT_SHA and digest(zero_raw)==ZERO_SHA,'both whole accepted parent equations')
    parent=json.loads(raw);zero=json.loads(zero_raw);child=load(HERE/'equation.json');cuts=load(HERE/'CUTS.json');verify_cuts(parent,child,cuts)
    verify_zero_cuts(zero,child,load(HERE/'ZERO_PARENT_CUTS.json'))
    for n,pin in load(HERE/'PROVENANCE.json')['dependencies'].items():
        data=(HERE/n).read_bytes();need(data==(ROOT/pin['repository_path']).read_bytes()and digest(data)==pin['sha256'],'whole ordinary/source dependency '+n)
    pins=load(HERE/'SOURCE_PINS.json')
    need(pins['direct_parent_equation_sha256']==PARENT_SHA and pins['direct_parent_manifest_sha256']==digest((PARENT/'MANIFEST.json').read_bytes())
         and pins['zero_parent_equation_sha256']==ZERO_SHA and pins['zero_parent_manifest_sha256']==digest((ZERO/'MANIFEST.json').read_bytes()),'both complete frozen parent/manifest pins')
    need(pins['ordinary_proof_sha256']==digest((HERE/'PROOF.md').read_bytes())and pins['generator_sha256']==digest((ROOT/pins['generator_repository_path']).read_bytes()),'proof and producer source pins')
    for n,h in load(HERE/'BUILD.json')['sha256'].items():need(digest((HERE/n).read_bytes())==h,'whole generated artifact '+n)
    peer=load(HERE/'source/COMBINED_ORDINARY_PEER.json')
    need(peer['status']=='PASS'and peer['source_pins']['candidates/ten-positive-direct-zero-offset/PROOF.md']==digest((HERE/'PROOF.md').read_bytes()),'focused complete ordinary peer pins current proof')
    for n,h in peer['source_pins'].items():need(digest((ROOT/n).read_bytes())==h,'ordinary-peer exact dependency '+n)
    degrees,counts=topology(child);rows=child['source'];tail=rows[92:]
    helper=HERE/'source/independent_norm_oracle.py'
    need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent conjugate-product oracle')
    spec=importlib.util.spec_from_file_location('direct_zero105_independent_norm',helper);oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
    definitions={n:(op,a,b)for n,op,a,b in rows}
    def local(register,leaves,defs=None):
        defs=definitions if defs is None else defs
        memo=dict(leaves)
        def expand(v):
            if type(v)is int:return oracle.Poly(v)
            if v in memo:return memo[v]
            need(v in defs,'complete actual cut reaches a supplied leaf: '+v)
            op,a,b=defs[v];a,b=expand(a),expand(b)
            memo[v]=a+b if op=='+'else a-b if op=='-'else a*b
            return memo[v]
        return expand(register)
    mu,X,Y=[oracle.variable(j)for j in range(3)]
    need(local('Am1',dict(mu=mu,X=X,Y=Y)).t==(mu*(X*Y+Y)).t,
         'universal full shared-base identity; all other downstream rows retained')
    x,a,b,c,d,omega=[oracle.variable(j)for j in range(6)]
    expected=oracle.norm_oracle(x,[9*a,b,c]);actual=oracle.evaluate(tail,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N']
    need(actual.t==expected.t and len(expected.t)==35,'every coefficient of independent eight-conjugate weighted norm')
    roots=oracle.evaluate(tail,dict(fs=(3*a+b+c)**2,fa=9*a*a,fb=b*b,fc=c*c))['N']
    need(not roots.t,'universal weighted signed-root zero identity')
    def sub(p,vals):
        out=0
        for m,c in p.t.items():
            for v,e in zip(vals,m):c*=v**e
            out+=c
        return out
    need(sub(expected,[0,1,1,1,0,0])==2025,'unchanged complete triple-root obstruction')
    # Whole centered cancellation, with independent free ring parameters.
    P,H,n,V,K,B=[oracle.variable(j)for j in range(6)]
    Z=P*(H*(n+V)+K)+H*B;M=P*H;Z0=P*(H*n+K)+H*B
    leaves=dict(P1mu2=P,Hp=H,n=n,V=V,Kpos=K,brk=B)
    need(local('Znum',leaves).t==Z.t and local('Mtot',leaves).t==M.t,'entire actual center/cancellation cuts bound to literal gates')
    need((Z-M*V).t==Z0.t,'full universal center cancellation Z0=Z-MV')
    Q,Z0,M,V,Zunused,unused=[oracle.variable(j)for j in range(6)];Z=Z0+M*V
    leaves=dict(Q=Q,Znum=Z,Mtot=M,V=V)
    need(local('fs',leaves).t==((Q-1)*Z**2).t and local('fc',leaves).t==(M**2*(Q*V**2-1)).t,
         'entire actual fs/fc cuts before universal omega cancellation')
    need(((Q-1)*Z**2-M**2*(Q*V**2-1)).t==(Q*Z0**2+2*Q*Z0*M*V-Z**2+M**2).t,'complete omega cancellation identity')
    # Derive every relevant upper bound from the literal front, no sampled degree.
    dz0_first=degrees['P1mu2']+max(degrees['Hp']+1,degrees['Kpos'])
    dz0_second=degrees['Hp']+max(degrees['mu2']+max(degrees['qbJ']+1,degrees['q3']+degrees['W']+degrees['B'],degrees['bJ']+degrees['X']),degrees['P1']+degrees['e'])
    dz0=max(dz0_first,dz0_second)
    omega_degrees=[degrees['Q']+2*dz0,degrees['Q']+dz0+degrees['Mtot']+degrees['V'],2*degrees['Znum'],2*degrees['Mtot']]
    need((dz0_first,dz0_second,dz0)==(14,24,24)and omega_degrees==[74,85,70,26],'entire omega upper bound and unique degree85 product')
    x,a,b,c,d,omega=[oracle.variable(j)for j in range(6)]
    centered=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N'];weights=(48,68,70,0,0,85)
    maximum=max(sum(e*w for e,w in zip(m,weights))for m in centered.t)
    top={m:c for m,c in centered.t.items()if sum(e*w for e,w in zip(m,weights))==maximum}
    need(maximum==340 and top=={(0,0,0,0,0,4):1},'whole centered norm unique leadingomega4, degree340')
    x,a,b,c,d,omega=[oracle.variable(j)for j in range(6)]
    need(local('Dtau',dict(V0=x,k=a)).t==(1+x*(x+1)*a*a).t,'full literal first-radicand cut')
    need(local('Df',dict(Dp=x,I=a)).t==(1+x*a*a).t and local('Q',dict(Dp=x,I=a)).t==(x*x*a*a).t,
         'full literal strong/auxiliary coefficient cuts')
    # Full leading product including eta+zeta. Small formal polynomials, not the
    # gigantic actual numeral expansion. Setting q=beta*J transfers its coefficient.
    saved=oracle.ZERO;oracle.ZERO=(0,)*9
    try:
        def var9(j):return oracle.Poly({tuple(int(k==j)for k in range(9)):1})
        q,x,Y,eta,zeta,F,alpha,i,K=[var9(j)for j in range(9)]
        X0=q+x;k=eta+zeta;A0=q*q*X0*Y;I0=i*(k*Y)**2;H0=4*A0
        B0=(q*K+X0)*(q-F-alpha)-q*F;R0=q**3*(q-F)
        Q0=A0**4*I0**2;V0=-A0**2*I0**2*R0;W0=q*q*H0*I0;Z00=-H0*q**7*W0*B0;M0=H0*q**9
        leading=2*Q0*Z00*M0*V0
        factored=2**7*q**39*X0**9*i**5*Y**19*k**10*B0*(q-F)
        need(leading.t==factored.t,'complete degree85 leading product including full eta+zeta and K0')
        need(max(m[1]for m in leading.t)==10,'complete omega maximumxdegree10')
        topx=oracle.Poly({tuple(0 if j==1 else e for j,e in enumerate(m)):v for m,v in leading.t.items()if m[1]==10})
        need(all(m[8]==0 for m in topx.t),'highestxpart independentofK0')
        fourth=topx**4
        need(fourth.t.get((156,0,76,40,0,4,4,20,0))==2**28,'nonzero exact degree340 selected coefficient')
        leading_terms=len(leading.t);topx_terms=len(topx.t);fourth_terms=len(fourth.t)
    finally:oracle.ZERO=saved
    # Universal ratio-cut algebra used in the NEW ordinary proof.
    lam,X,Y,k,I,b=[oracle.variable(j)for j in range(6)];a=Y*(X+1);A=lam*a+1;P=2*X*lam**2*Y**2+1
    need(((2*A-1)**2*X-(X+1)**2*(2*P)).t==(4*lam*a*X+X-2*(X+1)**2).t,'complete zero-offset lower-ratio cut')
    need((4*X*(X+1)+X-2*(X+1)**2).t==(2*X**2+X-2).t,'strict positive lower-ratio margin polynomial')
    need((lam*(a+1)-A).t==(lam-1).t,'zero-offset upper-ratio comparison')
    need((2*X*lam**2*Y**2+1-A).t==(lam*Y*(2*lam*X*Y-X-1)).t,'first-norm base strictly above newA')
    # Modulo mu, the newA is1 exactly and all normalized radicands unchanged.
    mu=oracle.Poly(0);A=mu*Y*(X+1)+1;Delta=A*A-1
    V0=X*mu*mu*Y*Y;Dtau=1+V0*(V0+1)*k*k;Df=1+Delta*I*I;Q=Delta*Delta*I*I;delta=Q-1;Dnum=Q*b*b-1
    need((9*delta*Dtau).t==oracle.Poly(-9).t and(delta*Df).t==oracle.Poly(-1).t and Dnum.t==oracle.Poly(-1).t,
         'all normalized radicand residues(-9,-1,-1) aftermu0')
    # Direct-carrier universal identities, with no arithmetic divisibility premise.
    q,K,w,C,F,L=[oracle.variable(j)for j in range(6)];X=q*w;Bt=(K+w)*C-F
    need((((q*K+X)*C-q*F)-q*Bt).t=={},'complete B=qBt identity')
    need((q+(X-q)-X).t=={},'direct positive-base coordinate algebra')
    need(((1+q*(q-1)*L)-(1+(q-1)*L)).t==((q-1)**2*L).t,'whole W difference')
    need(local('B',dict(q=q,K0=K,X=X,C=C,F=F)).t==(q*Bt).t,'actual complete B cut linked to99 transport')
    need(local('W',dict(q=q,bJ=q-1,L=L)).t==(1+q*(q-1)*L).t,'actual complete enlarged W cut')
    need(local('P1',dict(q=q,bJ=q-1)).t==(q**4*(q-1)).t,'actual whole q4 carrier')
    olddefs={n:(op,a,b)for n,op,a,b in zero['source']}
    need(local('Bt',dict(K0=K,w=w,C=C,F=F),olddefs).t==Bt.t,'actual complete old99 transport cut')
    need(local('W',dict(bJ=q-1,L=L),olddefs).t==(1+(q-1)*L).t,'actual complete old99 W cut')
    need(local('P1',dict(q=q,bJ=q-1),olddefs).t==(q**3*(q-1)).t,'actual complete old99 carrier')
    q,Y,W,B,X,unused=[oracle.variable(j)for j in range(6)];residue=q*(q-1)*Y-q**3*W*B-(q-1)*X
    need((residue+(q-1)*X).t==(q*((q-1)*Y-q*q*W*B)).t,'primitive modq remainder before cancellation')
    need(local('inner',dict(q=q,bJ=q-1,Y=Y,W=W,B=B,X=X)).t==residue.t,'complete literal primitive numerator cut')
    x,a,b,c,unused,omega=[oracle.variable(j)for j in range(6)]
    norm=oracle.evaluate(tail,dict(fs=x,fa=a,fb=b,fc=c))['N']
    scaled=oracle.evaluate(tail,dict(fs=omega**2*x,fa=omega**2*a,fb=omega**2*b,fc=omega**2*c))['N']
    need(scaled.t==(omega**8*norm).t,'entire norm q8homogeneity')
    saved=oracle.ZERO;oracle.ZERO=(0,)*8
    try:
        def var8(j):return oracle.Poly({tuple(int(k==j)for k in range(8)):1})
        q,H,mu,dW,t,u,Bt,X=[var8(j)for j in range(8)]
        lhs=H*mu**2*(q**4*(q-1)*(dW*t+u)-q**4*dW*Bt-(q-1)*X)
        rhs=H*mu**2*(q**4*dW*((q-1)*t-Bt)+(q-1)*(q**4*u-X))
        need(lhs.t==rhs.t,'complete licensed integer numerator cut')
    finally:oracle.ZERO=saved
    binding=load(HERE/'coefficients/BINDING.json');need(binding==parent['coefficient_binding']==child['coefficient_binding'],'entire originalcompact44 binding')
    ports={};payloads={}
    for name,pin in binding['ports'].items():
        blob=(HERE/'coefficients'/pin['file']).read_bytes();data=gzip.decompress(blob)
        need(blob==(PARENT/'coefficients'/pin['file']).read_bytes()and digest(blob)==pin['gzip_sha256']and digest(data)==pin['raw_sha256'],'whole compressed/raw coefficient payload '+name)
        value=int.from_bytes(data,'little');need(value.bit_length()==pin['bits'],'complete coefficient width')
        ports[name]=value;payloads[name]=pin['raw_sha256']
    need(ports['beta']==2**590069-1 and ports['beta']>=31 and ports['K0']>0 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'all exact uniform coefficient-port hypotheses')
    rng=random.Random(105340);modular=integer=carrier=exact_carrier=0
    preserved=['X','R','I','Df','Q','delta','V','Dnum','Dtau','L','Kpos','Am1','Hp','c','Dp']
    for prime in[1009,(1<<127)-1]:
        for _ in range(60):
            inputs={v:rng.randrange(-10,11)for v in child['witnesses']}|{k:v%prime for k,v in ports.items()}
            env=evaluate(rows,inputs,prime);independent=scalar_spec(inputs)
            need(all((env[n]-v)%prime==0 for n,v in independent.items()),'complete actualtuple/freeinput scalar specification')
            before=evaluate(parent['source'],inputs,prime)
            need((env['Am1']-before['Am1']+2*env['mu'])%prime==0,'actual newA=direct107A-2mu transcription');modular+=1
        count=0
        while count<60:
            inputs={v:rng.randrange(-20,21)for v in zero['witnesses']}|{k:v%prime for k,v in ports.items()}
            old=evaluate(zero['source'],inputs,prime);q=old['q'];qm=old['bJ']
            if not q or not qm:continue
            changed={n:v for n,v in inputs.items()if n!='w'};changed['x']=(old['X']-q)%prime;new=evaluate(rows,changed,prime)
            need(all(new[n]==old[n]for n in preserved),'all sameX zero99 kernels and base preserved')
            need((new['B']-q*old['Bt'])%prime==0 and(new['Mtot']-q*old['Mtot'])%prime==0,'complete primitive transport/M scalings')
            t=old['Bt']*pow(qm,-1,prime)%prime;u=old['X']*pow(q,-4,prime)%prime
            changed['n']=(inputs['n']+(new['W']-old['W'])*t+u)%prime;restored=evaluate(rows,changed,prime)
            need((restored['Znum']-q*old['Znum'])%prime==0 and(restored['N']-pow(q,8,prime)*old['N'])%prime==0,'licensed zero99-to105 wholecenter/outputscaling')
            count+=1;carrier+=1
    for _ in range(50):
        inputs={v:rng.randrange(-2,3)for v in child['witnesses']+child['fixed_numerals']};env=evaluate(rows,inputs)
        need(all(env[n]==v for n,v in scalar_spec(inputs).items()),'exact free-signed integer scalar transcription');integer+=1
    for q in[32,64,128]:
        for u in[1,2,3]:
            w=q**3*u;inputs={v:1 for v in zero['witnesses']}|dict(beta=q-1,K0=(q-2)*(w+1),MC=1,MF=q,w=w,F=q-2)
            old=evaluate(zero['source'],inputs);need(old['Bt']==(q-1)*w,'explicit exactinteger quotientdiagnostic family')
            changed={n:v for n,v in inputs.items()if n!='w'};changed['x']=old['X']-q;new=evaluate(rows,changed)
            changed['n']=inputs['n']+(new['W']-old['W'])*w+u;restored=evaluate(rows,changed)
            need(restored['Znum']==q*old['Znum']and restored['N']==q**8*old['N'],'exactinteger licensed completecenter/outputscaling');exact_carrier+=1
    ratio_controls=0
    for X in[32,33,64]:
        for Y in[1,2,3]:
            for lam in[1,2,7]:
                a=Y*(X+1);A=lam*a+1;P=2*X*lam*lam*Y*Y+1
                for r in[1,2,4]:
                    ratio=Fraction(pell(A,2*r+1)[1],pell(P,r+1)[1]);xi=Fraction((X+1)**(2*r),X**r)
                    need(xi<ratio<xi*Fraction(a+1,a)**(2*r),'small exact-rational ratio diagnostic');ratio_controls+=1
    slices=[]
    for prime in[(1<<127)-1,(1<<89)-1]:
        fixed={k:v%prime for k,v in ports.items()};base={v:rng.randrange(1,prime)for v in child['witnesses']};direction={v:rng.randrange(1,prime)for v in child['witnesses']}
        values=[evaluate(rows,fixed|{v:(base[v]+t*direction[v])%prime for v in child['witnesses']},prime)['N']for t in range(386)]
        need(line_degree(values,prime)==340,'whole actualtuple supplemental degree340 line');slices.append(dict(prime_bits=prime.bit_length(),degree=340))
    rejected=[]
    for label,change in[
        ('wrongprimitiveP',lambda p:next(r for r in p['source']if r[0]=='P1').__setitem__(2,'q3')),
        ('wrongcarrysign',lambda p:next(r for r in p['source']if r[0]=='inner').__setitem__(1,'+')),
        ('wrongbaseoperand',lambda p:next(r for r in p['source']if r[0]=='Am1').__setitem__(3,'Y')),
        ('retainedprivateoffset',lambda p:p['source'].insert(12,['a2','+','a',2])),
        ('wrongnormsign',lambda p:p['source'][-1].__setitem__(1,'+')),
        ('changedpositiveinputdomain',lambda p:p.__setitem__('domain','natural integers')),
        ('individualpayloadsubstitution',lambda p:p['coefficient_binding']['ports']['K0'].__setitem__('bits',1))]:
        bad=deepcopy(child);change(bad)
        try:verify_cuts(parent,bad,cuts)
        except(ValueError,KeyError,IndexError):rejected.append(label)
        else:raise ValueError('corruption accepted '+label)
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,operations=105,
        operation_breakdown=counts,exact_degree=340,syntactic_degree=384,
        all107_parent_definitions_bound=True,deleted_private_parent_rows=[5,6,12],changed_parent_row=13,moved_shared_parent_row=18,
        universal_shared_base_identity=True,entire_polynomial_equal_to_unshared106_direct_zero_offset=True,
        norm_tail_operations=13,independent_weighted_norm_terms=35,universal_root_identity=True,
        universal_center_and_omega_identities=True,actual_literal_front_polynomial_cuts=7,Z0_degree_bound=24,omega_term_degree_bounds=omega_degrees,
        unique_centered_top='omega^4',complete_leading_omega_terms=leading_terms,complete_maximum_x_omega_terms=topx_terms,complete_maximum_x_output_terms=fourth_terms,
        actual_selected_coefficient='2^28*beta^156',actual_selected_monomial=dict(J=156,i=20,x=40,Y=76,eta=40,zeta=0,alpha=4,F=4),
        universal_zero_offset_ratio_cuts=4,normalized_mod_mu_residues=[-9,-1,-1],triple_obstruction=2025,
        universal_direct_carrier_cuts=6,actual_literal_carrier_cuts=7,all99_zero_parent_definitions_bound=True,
        full_licensed_numerator_identity=True,norm_q8_homogeneity=True,ordinary_peer_pins_current_proof=True,
        actual_tuple_modular_scalar_controls=modular,exact_free_signed_scalar_controls=integer,exact_rational_ratio_controls=ratio_controls,
        actual_tuple_zero99_carrier_controls=carrier,exact_integer_zero99_carrier_controls=exact_carrier,
        actual_tuple_degree_slices=slices,rejected_corruptions=rejected,whole_four_payloads=payloads,
        direct_parent_equation_sha256=PARENT_SHA,zero_parent_equation_sha256=ZERO_SHA,equation_sha256=digest((HERE/'equation.json').read_bytes()),
        ordinary_proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
        scope='Complete literal105 graph/cuts/coherentpayloads, universal sharing equality to unshared106directzerooffset, independent full norm/centered degree340, ratio/directcarrier identities and explicit conditional zero99 map. Unbounded positivezero/refutation equivalence is PROOF.md. No positive pointwise inverse, newLean/internal-ZFC endpoint, historical emitter or page change.')
    target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
