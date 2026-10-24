#!/usr/bin/env python3
"""Independent119-operation full-map/two-cut/cleared-norm checker."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PARENT_SHA='738c7adb164ecc7267bee75868f5ab49a9ce9c951684fd8761e0e0f790477828'


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()


def load(path):return json.loads(path.read_bytes())


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


def verify_map(parent,child,remap):
    old,new=parent['nodes'],child['nodes'];records=remap['all_parent_nodes']
    need([r['parent']for r in records]==list(range(len(old))),'every148parentnodecovered')
    mapping={r['parent']:r['child']for r in records if r['status']=='retained'}
    removed={r['parent']for r in records if r['status']=='removed_private'}
    tau=remap['first_norm_cut'];radix=remap['radix_square_cut']
    need(removed==set(tau['deleted_parent'])|{radix['deleted_parent']}and len(removed)==4,
         'exactfourprivateremovals')
    need(not removed.intersection(parent['named_registers'].values()),'nopublicregisterremoved')
    need(sorted(list(mapping.values())+remap['inserted_child_nodes'])==list(range(len(new))),
         'complete146childnodecoverage')
    changed={tau['old_product_parent'],radix['M_parent']}
    for r in records:
        i=r['parent'];row=old[i]
        if i in removed:
            need(r['old_row']==row,'allremoveddefinitionsretainedforrestoration')
            continue
        need(r['changed_cut_definition']==(i in changed),'onlytwochangeddefinitions')
        if i not in changed:
            want=[row[0],mapping[row[1]],mapping[row[2]]]if row[0]in('add','sub','mul')else row
            need(new[mapping[i]]==want,'everyothernodecopiedwithalloperandsremapped')
    q,q2,two,M,twice=(radix[k]for k in('q_parent','existing_q2_parent','constant_two_parent','M_parent','deleted_parent'))
    need(old[q2]==['mul',q,q]and old[two]==['integer',2]and
         old[twice]==['mul',q,two]and old[M]==['mul',q,twice], 'completeMcutpremises')
    need(new[mapping[M]]==['mul',mapping[two],mapping[q2]]and radix['new_M_child']==mapping[M],
         'newMreusestheearlierq²')
    ell,k,p=(tau[x]for x in('ell_parent','k_parent','old_product_parent'))
    ep,eprod,k2=tau['deleted_parent'];L,Lp=tau['new_L_child'],tau['new_Lplusk_child']
    one=next(i for i,r in enumerate(old)if r==['integer',1])
    need(old[ep]==['add',one,ell]and old[eprod]==['mul',ell,ep]and
         old[k2]==['mul',k,k]and old[p]==['mul',eprod,k2],'completeDtaucutpremises')
    need(new[L]==['mul',mapping[ell],mapping[k]]and new[Lp]==['add',L,mapping[k]]and
         new[mapping[p]]==['mul',L,Lp]and remap['inserted_child_nodes']==[L,Lp],
         'completenewfirstPellfactorization')
    expected_uses={ep:[eprod],eprod:[p],k2:[p],twice:[M]}
    for i,uses in expected_uses.items():
        need([j for j,r in enumerate(old)if r[0]in('add','sub','mul')and i in r[1:]]==uses,
             'removedprivateintermediatehasonlythedeclaredcutuses')
    need(child['output']==mapping[parent['output']]and
         child['named_registers']=={k:mapping[i]for k,i in parent['named_registers'].items()},
         'allnamedregistersandoutputremapped')
    return mapping,removed


def line_degree(values,p):
    degree,level=-1,0;values=list(values)
    while values:
        if values[0]:degree=level
        values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
    return degree


def main():
    raw=(HERE/'source/parent-equation.json').read_bytes()
    need(digest(raw)==PARENT_SHA,'entirefrozen121parent')
    parent=json.loads(raw);child=load(HERE/'equation.json');remap=load(HERE/'NODE_REMAP.json')
    provenance=load(HERE/'PROVENANCE.json')
    need(child['parent_sha256']==remap['parent_sha256']==provenance['parent_equation_sha256']==PARENT_SHA,
         'consistentcompleteparentpins')
    mapping,removed=verify_map(parent,child,remap)
    need(child['domain']==parent['domain']=='unrestricted integers'and
         child['variables']==parent['variables']and child['variable_count']==14,'same14integerunknowns')
    old,nodes=parent['nodes'],child['nodes'];nm=child['named_registers'];degrees=[]
    for i,r in enumerate(nodes):
        need(r[0]in('integer','variable','coefficient','add','sub','mul'),'polynomialnode')
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
    need(live==set(range(len(nodes))),'all146nodeslive')
    need([r[1]for r in nodes if r[0]=='variable']==child['variables'],'all14livevariables')
    ports=[r[1]for r in nodes if r[0]=='coefficient']
    need(len(ports)==6 and set(ports)=={'beta','K0','MC','MF','cone_A','cone_B'},'allsixliveports')
    counts=Counter(r[0]for r in nodes if r[0]in('add','sub','mul'))
    need(dict(counts)==child['operation_counts']=={'mul':68,'add':26,'sub':25}and
         sum(counts.values())==child['operations']==119,'actual119operations')
    need(degrees[child['output']]==344 and degrees[nm['N']]==288 and
         child['exact_degree']==312 and child['norm_exact_degree']==256,'unchangeddegreecontracts')
    helper=HERE/'source/independent_norm_oracle.py'
    need(digest(helper.read_bytes())==provenance['oracle_sha256'],'independentringoraclepin')
    spec=importlib.util.spec_from_file_location('independent_sparse_ring_oracle',helper)
    oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
    q,ell,k,_,_,_=[oracle.variable(i)for i in range(6)]
    need((q*(2*q)).t==(2*(q*q)).t,'universalMcutidentity')
    need((ell*(ell+1)*(k*k)).t==((ell*k)*((ell*k)+k)).t,
         'universalDtaucutidentity')
    need((ell*(ell+1)*(k*k)).t!=((ell*k)*((ell*k)-k)).t,
         'mutatedDtauplusoperationactuallyrejected')
    need((q*(2*q)).t!=(q*q).t,'missingfactor2actuallyrejected')
    x,a,b,c,delta,_=[oracle.variable(i)for i in range(6)]
    env={i:oracle.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
    for name,value in(('center',x),('raw_A',a),('raw_B',b),('Cn',c),('delta',delta)):
        env[nm[name]]=value
    start=max(nm[name]for name in('center','raw_A','raw_B','Cn'))+1
    for i in range(start,nm['N']+1):
        r=nodes[i]
        if r[0]=='integer':continue
        need(r[1]in env and r[2]in env,'normcutfullybound')
        u,v=env[r[1]],env[r[2]];env[i]=u+v if r[0]=='add'else u-v if r[0]=='sub'else u*v
    fraction=oracle.Poly({(0,0,0,1,-1,0):1})
    expected=delta**4*oracle.norm_oracle(x,[a,b,fraction])
    need(env[nm['N']].t==expected.t and len(expected.t)==35,'full35termclearednormunchanged')
    binding=load(HERE/child['coefficient_binding']);coefficients={};payloads={}
    for name,pin in binding['payloads'].items():
        blob=(HERE/'coefficients'/pin['file']).read_bytes();data=gzip.decompress(blob)
        need(digest(data)==pin['raw_sha256']and len(data)==pin['raw_bytes'],'wholeactualpayload')
        value=int.from_bytes(data,'little');need(value.bit_length()==pin['bits'],'actualpayloadwidth')
        coefficients[name]=value;payloads[name]=dict(raw_sha256=digest(data),bits=value.bit_length())
    need(len(coefficients)==6 and coefficients['beta']==2**1064921-1 and
         coefficients['cone_A']==2**1113 and coefficients['cone_B']==2**666104,'originalsix-porttuple')
    rng=random.Random(119312);controls=free_controls=0
    for prime in(1009,(1<<127)-1):
        for i in range(50):
            inp={v:rng.randrange(-20,21)for v in child['variables']}
            if i%4==0:inp['v']=0
            if i%5==0:inp['c']=0
            inp.update({v:c%prime for v,c in coefficients.items()})
            want,have=evaluate(old,inp,prime),evaluate(nodes,inp,prime)
            need(all(want[i]==have[j]for i,j in mapping.items()),'everyretainednodeequalafterbothcuts')
            restored={i:have[j]for i,j in mapping.items()}
            for i in sorted(removed):
                r=old[i];u,v=restored[r[1]],restored[r[2]]
                restored[i]=(u+v if r[0]=='add'else u-v if r[0]=='sub'else u*v)%prime
                need(restored[i]==want[i],'everyprivateoldnoderestoredfromrecordeddefinition')
            need(want[parent['output']]==have[child['output']],'wholeoutputequal')
            controls+=1
    for _ in range(50):
        inp={v:rng.randrange(-2,3)for v in child['variables']+ports}
        want,have=evaluate(old,inp),evaluate(nodes,inp)
        need(all(want[i]==have[j]for i,j in mapping.items()),'allretainednodeswithfreesignedcoefficients')
        free_controls+=1
    slices=[]
    for prime in((1<<127)-1,(1<<89)-1):
        base={v:rng.randrange(1,prime)for v in child['variables']}
        direction={v:rng.randrange(1,prime)for v in child['variables']}
        ports0={v:c%prime for v,c in coefficients.items()};pv=[];nv=[]
        for t in range(346):
            values=evaluate(nodes,ports0|{v:(base[v]+t*direction[v])%prime for v in child['variables']},prime)
            pv.append(values[child['output']]);nv.append(values[nm['N']])
        dp,dn=line_degree(pv,prime),line_degree(nv,prime)
        need((dp,dn)==(312,256),'actualsixportfinalandnormdegrees')
        slices.append(dict(prime_bits=prime.bit_length(),final_degree=dp,norm_degree=dn))
    corrupt=deepcopy(child);cut=remap['radix_square_cut'];corrupt['nodes'][cut['new_M_child']][1]=0
    try:verify_map(parent,corrupt,remap)
    except ValueError:pass
    else:raise ValueError('corruptedMoperandaccepted')
    proof_pin=digest((HERE/'source/ordinary-proof.md').read_bytes())
    need(provenance['ordinary_proof_sha256']==proof_pin,'samecorrectedsignedproof')
    for name in('parent-check.json','parent-check-optimized.json'):
        receipt=load(HERE/'source'/name)
        need(receipt['status']=='PASS'and receipt['equation_sha256']==PARENT_SHA and
             receipt['ordinary_proof_sha256']==proof_pin,'completefrozen121parentreceipts')
    for name in('proof-peer.json','proof-peer-optimized.json'):
        peer=load(HERE/'source'/name)
        need(peer['status']=='PASS'and peer['ordinary_proof_sha256']==proof_pin,'independentsignedpeerproofpin')
    for name,pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/name).read_bytes())==pin,'generatedartifactseal '+name)
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),integer_variables=14,
        operations=119,operation_counts=dict(counts),exact_degree=312,norm_degree=256,
        syntactic_bound=344,norm_syntactic_bound=288,parent_nodes=148,child_nodes=146,
        all_parent_nodes_accounted=True,all_child_nodes_accounted=True,
        private_removed_nodes=sorted(removed),universal_two_cut_identities=True,
        unchanged_complete_norm_coefficients=len(expected.t),actual_all_node_controls=controls,
        free_signed_coefficient_controls=free_controls,actual_tuple_degree_slices=slices,
        mutated_cut_sign_factor_and_operand_rejected=True,whole_six_payloads=payloads,
        ordinary_proof_sha256=proof_pin,parent_equation_sha256=PARENT_SHA,
        equation_sha256=digest((HERE/'equation.json').read_bytes()),
        scope='Exact universal complete-polynomial identity with121parent fromtwoalgebraiccuts and complete148-to146nodecoverage. Authentic sixcoefficients and signedordinaryproof unchanged. No new native calibration, Lean or internal-ZFC proof.')
    target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json'
    (HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
