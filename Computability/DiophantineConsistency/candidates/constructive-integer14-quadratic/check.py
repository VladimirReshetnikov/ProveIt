#!/usr/bin/env python3
"""Independent signed14 literal, cleared-octic, payload and leading-form controls."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from math import factorial
from pathlib import Path
import random
import sys
import zipfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
PARENT_SHA='0e9f89dfdcc8a27feed8a278d46b04b10c88d24cec76a190444eb9b7e2b0fa7b'


def need(ok,message):
    if not ok:raise ValueError(message)


def load(path):return json.loads(path.read_bytes())


def digest(raw):return sha256(raw).hexdigest()


def evaluate(nodes,inputs,prime=None):
    values=[]
    for row in nodes:
        if row[0]=='integer':v=row[1]
        elif row[0]in('variable','coefficient'):v=inputs[row[1]]
        else:
            a,b=values[row[1]],values[row[2]]
            v=a+b if row[0]=='add'else a-b if row[0]=='sub'else a*b
        values.append(v if prime is None else v%prime)
    return values


def pell(A,n):
    # Binary powering also for negative A and signed n.
    sign=1 if n>=0 else-1;n=abs(n)
    D=A*A-1;x,y,u,v=1,0,A,1
    while n:
        if n&1:x,y=x*u+D*y*v,x*v+y*u
        u,v=u*u+D*v*v,2*u*v;n//=2
    return x,sign*y


def lemma_controls():
    folds=main=projections=heights=odd=0
    for A in list(range(-12,-2))+list(range(3,13)):
        B=abs(A);D=B*B-1
        for m in range(1,7):
            f,I=pell(B,m);S=D*I
            need(f>2*I,'absolute strong-root height')
            for v in range(-4*m,4*m+1):
                q,t=divmod(v,2*m);p=min(t,2*m-t);eps=-1 if q%2 else 1
                need((pell(B,v)[1]-eps*pell(B,p)[1])%f==0,'all signed-indexfolds')
                folds+=1
            for h in range(4*m+1):
                nu=2*h+1;chi,y=pell(S,nu);need(chi%S==0,'oddauxiliaryindex')
                absV=chi//S
                need((absV-(-1)**h*pell(B,nu)[1])%f==0,'oddpolynomialreduction')
                for sgnV in(-1,1):
                    residue=(-sgnV*absV)%f
                    for c in(residue,residue-f):
                        if not 0<abs(c)<=I:continue
                        need(any(pell(B,p)[1]==abs(c)for p in range(1,m+1)),
                             'mainclassificationforbothsignedc/V/A')
                        main+=1
        H=4*A-5;a=A-2
        for R in range(1,32,2):
            chi,psi=pell(A,R);Bpow=2**R
            need(psi==pell(abs(A),R)[1],'oddpsiindependentofAsign')
            for sigma in(-1,1):
                c=sigma*psi;d=sigma*chi
                for X in(-Bpow-1,-Bpow,-Bpow+1,-1,1,Bpow-1,Bpow,Bpow+1):
                    K=X*(X+2*a*c)-1;Z=sigma*X
                    need((Bpow*K-(Z-Bpow)*(Bpow*Z+1))%abs(H)==0,
                         'fullsignedquadraticprojectionproduct')
                    if Z==Bpow:need((d-X-a*c)%abs(H)==0,'signedmainprojectionrestored')
                    projections+=1
    for x in(64,65,128,1024):
        for r in(10,11,24,25,48):
            R=2*r+1;power=(x-3)**r;m=power//2
            Hlower=4*(x-1)*m-3
            need(m>power/2-1 if power.bit_length()<50 else 2*m>power-2,'strictintegerweakratio')
            need(Hlower>3*x*m>x*power>2**(2*R+2)*x*x,'signedwholeproductheight')
            heights+=1
    for R in range(1,11):
        for Z in range(-100,101):
            need((2**R*Z+1)%2==1 and 2**R*Z+1!=0,'oddsecondfactorfornegativeZtoo')
            odd+=1
    return dict(signed_index_folds=folds,signed_main_recoveries=main,
        signed_projection_cases=projections,whole_product_height_cases=heights,
        negative_and_positive_Z_odd_factor_cases=odd,
        scope='Finite diagnostics only; the all-index proof and signed bootstrap are PROOF.md.')


def leading(e,p):
    q=6*e['beta']*e['j']%p;W=12*e['w']%p;X=q*W%p;Y=q*e['v']%p
    a=X*Y%p;i=2*e['r']%p
    R=(pow(q,4,p)*e['z']-pow(q,3,p)*W*e['C'])%p
    k=(R+e['h']*a)%p;eta=-Y*k%p
    Q=pow(a,4,p)*i*i*pow(e['c'],4,p)%p
    V=-a*a*i*i*pow(e['c'],4,p)*R%p
    L=X*Y*Y*k%p;U=8*q*q*a%p
    N=16*pow(Q,4,p)*pow(U,8,p)*pow(V,4,p)*pow(L,4,p)%p
    return N,N*pow(eta,8,p)%p


def line_data(values,p):
    degree,difference,level=-1,None,0;values=list(values)
    while values:
        if values[0]:degree,difference=level,values[0]
        values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
    return degree,difference


def main():
    raw=(HERE/'source/parent-equation.json').read_bytes()
    need(digest(raw)==PARENT_SHA,'complete145parent')
    parent=json.loads(raw);child=load(HERE/'equation.json')
    remap=load(HERE/'PREFIX_REMAP.json');provenance=load(HERE/'PROVENANCE.json')
    need(child['parent_sha256']==remap['parent_sha256']==provenance['parent_equation_sha256']==PARENT_SHA,
         'consistentparentpins')
    old,nodes=parent['nodes'],child['nodes'];pn=parent['named_registers'];nm=child['named_registers']
    need(child['domain']==parent['domain']=='unrestricted integers'and
         child['variables']==parent['variables']and child['variable_count']==14,'same14integerdomain')
    need(remap['parent_prefix_last']==pn['Cn'],'completeprefixboundary')
    deleted={pn['Dmain']-1,pn['Dmain'],pn['Dm']-1,pn['Dm']}
    need({r['parent']for r in remap['deleted_prefix']}==deleted,'allfourmainrootgatesremoved')
    for r in remap['deleted_prefix']:need(old[r['parent']]==r['row'],'literaldeletedgate')
    retained=remap['retained_prefix'];mapping={r['parent']:r['child']for r in retained}
    projection=remap['replaced_projection'];mapping[pn['b0']]=projection['new_K']
    need(projection['parent']==pn['b0']and projection['old_row']==old[pn['b0']],
         'completeoldprojectioncut')
    need([r['parent']for r in retained]==[i for i in range(pn['Cn']+1)
            if i not in deleted and i!=pn['b0']],'everyretainedprefixcovered')
    for entry in retained:
        i,j=entry['parent'],entry['child'];r=old[i]
        want=[r[0],mapping[r[1]],mapping[r[2]]]if r[0]in('add','sub','mul')else r
        need(nodes[j]==want,'everyretaineddefinitionandalloperandsremapped')
    indices=projection['child_indices']
    need(len(indices)==4 and projection['new_rows']==[nodes[i]for i in indices],
         'completefourgateKprojection')
    c1=next(i for i,r in enumerate(nodes)if r==['integer',1])
    c2=next(i for i,r in enumerate(nodes)if r==['integer',2])
    X=mapping[pn['X']];ac=mapping[old[pn['b0']][2]]
    need([nodes[i]for i in indices]==[
        ['mul',c2,ac],['add',X,indices[0]],['mul',X,indices[1]],['sub',indices[2],c1]],
        'literalKequalsX(X+2ac)-1')
    need(sorted([r['child']for r in retained]+indices)==list(range(remap['child_prefix_length'])),
         'completechildprefixcoverage')
    need(remap['old_norm_indices']==list(range(pn['Cn']+1,pn['N']+1)),
         'completeoldnormreplacement')
    norm_indices=remap['new_norm_indices']
    need(norm_indices==list(range(remap['child_prefix_length'],nm['N']+1)),
         'completenewnormcoverage')
    mapping[pn['N']]=nm['N']
    for entry in remap['finalizer']:
        i,j=entry['parent'],entry['child'];r=old[i]
        need(nodes[j]==[r[0],mapping[r[1]],mapping[r[2]]],'unchangedfinalizercopy')
        mapping[i]=j
    need([r['parent']for r in remap['finalizer']]==list(range(pn['N']+1,len(old)))and
         [r['child']for r in remap['finalizer']]==list(range(nm['N']+1,len(nodes))),
         'completefinalizercoverage')
    need(mapping[parent['output']]==child['output'],'correctfinaloutput')
    degrees=[]
    for i,r in enumerate(nodes):
        need(r[0]in('variable','integer','coefficient','add','sub','mul'),'polynomialnode')
        if r[0]in('add','sub','mul'):
            need(all(type(j)is int and 0<=j<i for j in r[1:]),'topologicalgate')
            degrees.append(degrees[r[1]]+degrees[r[2]]if r[0]=='mul'else max(degrees[r[1]],degrees[r[2]]))
        else:degrees.append(1 if r[0]=='variable'else 0)
    live=set();todo=[child['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0]in('add','sub','mul'):todo.extend(nodes[i][1:])
    need(live==set(range(len(nodes))),'allnodeslive')
    counts=Counter(r[0]for r in nodes if r[0]in('add','sub','mul'))
    need(dict(counts)==child['operation_counts']=={'mul':70,'add':26,'sub':25}and
         sum(counts.values())==child['operations']==121,'actualcomplete121operations')
    need(degrees[child['output']]==344 and degrees[nm['N']]==288,'syntacticbounds')
    helper=HERE/'source/independent_norm_oracle.py'
    need(digest(helper.read_bytes())==provenance['oracle_sha256'],'independentoraclepin')
    spec=importlib.util.spec_from_file_location('independent_sparse_ring_oracle',helper)
    oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
    x,a,b,c,delta,_=[oracle.variable(i)for i in range(6)]
    def norm_eval(literal_nodes):
        env={i:oracle.Poly(r[1])for i,r in enumerate(literal_nodes)if r[0]=='integer'}
        for name,value in(('center',x),('raw_A',a),('raw_B',b),('Cn',c),('delta',delta)):
            env[nm[name]]=value
        for i in norm_indices:
            r=literal_nodes[i]
            if r[0]=='integer':continue
            need(r[1]in env and r[2]in env,'allnormcutportsbound')
            u,v=env[r[1]],env[r[2]]
            env[i]=u+v if r[0]=='add'else u-v if r[0]=='sub'else u*v
        return env[nm['N']]
    fraction=oracle.Poly({(0,0,0,1,-1,0):1})
    expected=delta**4*oracle.norm_oracle(x,[a,b,fraction])
    need(norm_eval(nodes).t==expected.t and len(expected.t)==35 and
         all(all(e>=0 for e in mon)for mon in expected.t),'whole35termdenominatorclearedoctic')
    corrupt=deepcopy(nodes);corrupt[nm['N']][0]='add'
    need(norm_eval(corrupt).t!=expected.t,'mutatednormpolarityactuallyevaluatedandrejected')
    aa,cc,XX,DD,BB,_=[oracle.variable(i)for i in range(6)]
    HH=4*aa+3;DDmain=(aa*aa+HH)*cc*cc+1;KK=XX*(XX+2*aa*cc)-1
    need(((XX+aa*cc)**2-DDmain).t==(KK-HH*cc*cc).t,'exactsquaredprojectionidentity')
    need((BB*KK-(XX-BB)*(BB*XX+1)).t==
         (XX*((BB*(DD+aa*cc)-1)-BB*(DD-aa*cc-BB))).t,
         'clearedproductlinearcombinationwithoutnonunitcancellation')
    badK=XX*(XX+2*aa*cc)+1
    need(((XX+aa*cc)**2-DDmain).t!=(badK-HH*cc*cc).t,
         'mutatedKplus1actuallyevaluatedandrejected')
    binding=load(HERE/child['coefficient_binding']);coefficients={};payloads={}
    need(len(binding['payloads'])==6,'completesixfixedports')
    for name,pin in binding['payloads'].items():
        blob=(HERE/'coefficients'/pin['file']).read_bytes();data=gzip.decompress(blob)
        need(digest(data)==pin['raw_sha256']and len(data)==pin['raw_bytes'],'authenticwholepayload')
        coefficients[name]=int.from_bytes(data,'little')
        need(coefficients[name].bit_length()==pin['bits'],'actualpayloadbitwidth')
        payloads[name]=dict(raw_sha256=digest(data),bits=pin['bits'])
    need(coefficients['beta']==2**1064921-1 and coefficients['cone_A']==2**1113 and
         coefficients['cone_B']==2**666104,'originalbetaandbothcones')
    rng=random.Random(121312);contracts=0
    changed={pn['b0']}
    for i,r in enumerate(old[:pn['Cn']+1]):
        if r[0]in('add','sub','mul')and any(j in changed for j in r[1:]):changed.add(i)
    for p in(1009,(1<<127)-1):
        for k in range(50):
            inp={v:rng.randrange(-20,21)for v in child['variables']}
            if k%4==0:inp['v']=0
            if k%5==0:inp['c']=0
            inp.update({v:c%p for v,c in coefficients.items()})
            oldv,newv=evaluate(old,inp,p),evaluate(nodes,inp,p)
            need(all(oldv[r['parent']]==newv[r['child']]for r in retained
                     if r['parent']not in changed),'allunaffectedprefixvalues')
            def val(name):return newv[nm[name]]
            K=val('X')*(val('X')+2*val('a')*val('c'))-1
            Z=val('U')*(inp['n']+val('V'))+val('M')*K+val('H')*(inp['v']-val('q')**2)
            need(val('K')==K%p and val('center')==Z%p,'independentfullprojectioncenterformula')
            s,u,t,w=[val(k)for k in('fs','fa','fb','fc')]
            N=((s+w-u-t)**2-4*(s*w+u*t))**2-64*s*w*u*t
            need(val('N')==N%p and newv[child['output']]==
                 (val('S')+N+val('S')*N)%p,'independentwholeocticandfinalizer')
            contracts+=1
    slices=[]
    for p in((1<<127)-1,(1<<89)-1):
        for _ in range(2):
            base={v:rng.randrange(1,p)for v in child['variables']}
            direction={v:rng.randrange(1,p)for v in child['variables']}
            ports={v:c%p for v,c in coefficients.items()};Pvals=[];Nvals=[]
            for t in range(346):
                e=evaluate(nodes,ports|{v:(base[v]+t*direction[v])%p for v in child['variables']},p)
                Pvals.append(e[child['output']]);Nvals.append(e[nm['N']])
            dn,cn=line_data(Nvals,p);dp,cp=line_data(Pvals,p);wantN,wantP=leading(ports|direction,p)
            need((dn,dp)==(256,312),'actualsixportnormandfinaldegrees')
            need(cn*pow(factorial(256)%p,-1,p)%p==wantN and
                 cp*pow(factorial(312)%p,-1,p)%p==wantP,'bothactualleadingcoefficientsmatchunboundedformula')
            slices.append(dict(prime_bits=p.bit_length(),norm_degree=dn,final_degree=dp,leading_forms_match=True))
    controls=lemma_controls()
    archive=REPO/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
    need(digest(archive.read_bytes())==provenance['archive_sha256'],'originalwholearchivepin')
    with zipfile.ZipFile(archive)as z:
        need(z.read(provenance['borrowed_member'])==(HERE/'source/RESIDUE_AND_DETERMINANT.md').read_bytes(),
             'exactborrowedsignedbootstrapprefixsource')
    for name in('parent-check.json','parent-check-optimized.json'):
        receipt=load(HERE/'source'/name)
        need(receipt['status']=='PASS'and receipt['equation_sha256']==PARENT_SHA,'frozen145parentreceipts')
    for name,pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/name).read_bytes())==pin,'generatedartifactseal '+name)
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),integer_variables=14,
        operations=121,operation_counts=dict(counts),exact_degree=312,norm_degree=256,
        syntactic_bound=344,norm_syntactic_bound=288,full_prefix_and_norm_finalizer_coverage=True,
        complete_cleared_octic_coefficients=len(expected.t),exact_projection_identities=True,
        mutated_norm_polarity_and_K_constant_rejected=True,
        actual_tuple_whole_formula_controls=contracts,actual_tuple_leading_degree_slices=slices,
        signed_lemma_controls=controls,whole_six_payloads=payloads,
        borrowed_prefix_sha256=provenance['borrowed_prefix_sha256'],
        ordinary_proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
        equation_sha256=digest((HERE/'equation.json').read_bytes()),
        scope='Exact symbolic/literal/wholepayload certificates and finite signedproofcontrols. Unbounded unrestricted-integer-zero-existence equivalence is PROOF.md; not a full-output identity withparent. No Lean/internalZFC/nativecalibration claim.')
    target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json'
    (HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
