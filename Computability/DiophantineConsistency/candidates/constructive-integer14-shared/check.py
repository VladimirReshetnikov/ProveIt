#!/usr/bin/env python3
"""Independent complete node-alias, six-port, cleared norm and degree checker."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random
import sys
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PARENT_SHA = '10327b2f4fc1589a86268583b1cdc3e59391b32051cecc5f1bf7140c6dea4269'


def need(ok,message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(raw):
    return sha256(raw).hexdigest()


def evaluate(nodes,inputs,prime=None):
    values=[]
    for row in nodes:
        op=row[0]
        if op=='integer':v=row[1]
        elif op in ('variable','coefficient'):v=inputs[row[1]]
        else:
            a,b=values[row[1]],values[row[2]]
            v=a+b if op=='add' else a-b if op=='sub' else a*b
        values.append(v if prime is None else v % prime)
    return values


def verify_remap(parent,child,remap):
    old,new=parent['nodes'],child['nodes']
    aliases={41:24,68:66}
    need(old[41]==['sub',25,22] and old[25]==['add',22,24] and
         old[22]==['integer',1] and old[24]==['mul',14,23], 'first exact cancellation premises')
    need(old[68]==['sub',67,22] and old[67]==['add',22,66] and
         old[66]==['mul',38,65], 'second exact cancellation premises')
    records=remap['all_parent_nodes']
    need([r['parent'] for r in records]==list(range(len(old))), 'all175parent nodes covered')
    mapping={r['parent']:r['child'] for r in records}
    need([r['child'] for r in records if not r['deleted_alias']]==list(range(len(new))),
         'all173child nodes covered once in order')
    for i,row in enumerate(old):
        j=mapping[i]
        need(records[i]['deleted_alias']==(i in aliases),'only the two specified aliases deleted')
        if i in aliases:
            need(j==mapping[aliases[i]],'deleted node maps to its earlier equal value')
        else:
            want=([row[0],mapping[row[1]],mapping[row[2]]]
                  if row[0] in ('add','sub','mul') else row)
            need(new[j]==want,'every retained leaf/gate copied with all operands remapped')
    need(child['output']==mapping[parent['output']],'complete output remap')
    need(child['named_registers']=={k:mapping[i]for k,i in parent['named_registers'].items()},
         'every named register remapped')
    return mapping


def norm_polynomial(packet,oracle):
    nodes,named=packet['nodes'],packet['named_registers']
    x,a,b,d,c,delta=[oracle.variable(i)for i in range(6)]
    env={i:oracle.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
    for name,value in zip(('center','A','B','Dm','Cn','delta'),(x,a,b,d,c,delta)):
        need(named[name] not in env,'distinct nonconstant norm cut')
        env[named[name]]=value
    start=max(named[name]for name in ('center','A','B','Dm','Cn'))+1
    for i in range(start,named['N']+1):
        row=nodes[i]
        if row[0]=='integer':continue
        need(row[0]in('add','sub','mul')and row[1]in env and row[2]in env,
             'all norm cut ports bound, no hidden free tail input')
        u,v=env[row[1]],env[row[2]]
        env[i]=u+v if row[0]=='add'else u-v if row[0]=='sub'else u*v
    fraction=oracle.Poly({(0,0,0,0,1,-1):1})
    expected=delta**8*oracle.norm_oracle(x,[a,b,d,fraction])
    need(all(all(e>=0 for e in mon)for mon in expected.t),'exact denominator clearing')
    need(env[named['N']].t==expected.t and len(expected.t)==495,
         'entire literal cleared norm equals all495 independent coefficients')
    return expected


def line_degree(values,prime):
    degree,level=-1,0
    values=list(values)
    while values:
        if values[0]:degree=level
        values=[(b-a)%prime for a,b in zip(values,values[1:])]
        level+=1
    return degree


def main():
    pins=load(HERE/'SOURCE_PINS.json')
    archive=REPO/pins['archive_path']
    need(digest(archive.read_bytes())==pins['archive_sha256'],'complete immutable original archive')
    with zipfile.ZipFile(archive)as z:
        component={n[len(pins['component_prefix']):]:z.read(n)for n in z.namelist()
                   if n.startswith(pins['component_prefix'])and not n.endswith('/')}
    need(len(component)==len(pins['all104_component_members'])==104,'complete104memberinventory')
    need({n:digest(b)for n,b in component.items()}==pins['all104_component_members'],
         'every full component member authenticated')
    raw=(HERE/'source/parent-equation.json').read_bytes()
    need(digest(raw)==PARENT_SHA and raw==component['crt14_degree568.json'],'entire original147graph')
    parent,child=json.loads(raw),load(HERE/'equation.json')
    remap=load(HERE/'NODE_REMAP.json')
    need(child['parent_sha256']==remap['parent_sha256']==PARENT_SHA,'consistent parent pins')
    mapping=verify_remap(parent,child,remap)
    need(child['domain']==parent['domain']=='unrestricted integers' and
         child['variables']==parent['variables']and child['variable_count']==14,'unchanged14integerdomain')
    nodes=child['nodes'];degrees=[]
    for i,row in enumerate(nodes):
        op=row[0]
        need(op in('integer','variable','coefficient','add','sub','mul'),'polynomial node')
        if op in('add','sub','mul'):
            need(all(type(j)is int and 0<=j<i for j in row[1:]),'topologicalbinarygate')
            degrees.append(degrees[row[1]]+degrees[row[2]]if op=='mul'else max(degrees[row[1]],degrees[row[2]]))
        else:degrees.append(1 if op=='variable'else 0)
    live=set();todo=[child['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0]in('add','sub','mul'):todo.extend(nodes[i][1:])
    need(live==set(range(len(nodes))),'allnodeslive')
    need([r[1]for r in nodes if r[0]=='variable']==child['variables'],'all14liveunknowns')
    ports=[r[1]for r in nodes if r[0]=='coefficient']
    need(len(ports)==6 and set(ports)=={'beta','K0','MC','MF','cone_A','cone_B'},'whole six live coefficientports')
    counts=Counter(r[0]for r in nodes if r[0]in('add','sub','mul'))
    need(dict(counts)==child['operation_counts']=={'add':30,'mul':88,'sub':27}and
         sum(counts.values())==child['operations']==145,'complete145operationcensus')
    need(child['exact_degree']==parent['exact_degree']==568 and
         child['norm_exact_degree']==parent['norm_exact_degree']==512 and degrees[child['output']]==632,
         'unchanged exactdegree and actual syntactic632bound')
    provenance=load(HERE/'PROVENANCE.json');helper=HERE/'source/independent_norm_oracle.py'
    need(digest(helper.read_bytes())==provenance['oracle_sha256'],'independent sparse ringoracle')
    spec=importlib.util.spec_from_file_location('independent_sparse_ring_oracle',helper)
    oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
    x=oracle.variable(0)
    need(((1+x)-1).t==x.t,'both generic subtractionaliases overZ')
    norm=norm_polynomial(child,oracle)
    need(norm_polynomial(parent,oracle).t==norm.t,'unchanged entire clearednorm')
    # The finalizer is retained exactly by the complete remap. Check its
    # two-variable identity without any numerical sign assumption on N.
    S,N=oracle.variable(0),oracle.variable(1)
    need((N+S+N*S).t==((1+S)*(1+N)-1).t,'unit-product finalizer ringidentity')
    binding=load(HERE/child['coefficient_binding'])
    need((HERE/child['coefficient_binding']).read_bytes()==component['upstream/coefficients/BINDING.json'],
         'whole original six-port binding')
    coefficients,payloads={},{}
    for name,record in binding['payloads'].items():
        blob=(HERE/'coefficients'/record['file']).read_bytes()
        need(blob==component['upstream/coefficients/'+record['file']],'whole original compressed payload')
        data=gzip.decompress(blob)
        need(digest(data)==record['raw_sha256']and len(data)==record['raw_bytes'],'whole rawpayload')
        value=int.from_bytes(data,'little')
        need(value.bit_length()==record['bits'],'actualpayloadbitwidth')
        coefficients[name]=value
        payloads[name]=dict(raw_sha256=digest(data),bits=value.bit_length())
    need(coefficients['beta']==2**1064921-1 and coefficients['cone_A']==2**1113 and
         coefficients['cone_B']==2**666104,'completebetaandbothconesrecipes')
    rng=random.Random(145568);diagnostics=0
    for prime in (1009,(1<<127)-1):
        for k in range(50):
            env={v:rng.randrange(-20,21)for v in child['variables']}
            if k%4==0:env['v']=0
            if k%5==0:env['c']=0
            env.update({v:c%prime for v,c in coefficients.items()})
            want,have=evaluate(parent['nodes'],env,prime),evaluate(nodes,env,prime)
            need(all(want[i]==have[j]for i,j in mapping.items()),'every175parentnodevalueequalsmappedchild')
            diagnostics+=1
    free_controls=0
    for _ in range(50):
        env={v:rng.randrange(-2,3)for v in child['variables']+ports}
        want,have=evaluate(parent['nodes'],env),evaluate(nodes,env)
        need(all(want[i]==have[j]for i,j in mapping.items()),'allnodesatsignedfreecoefficients')
        free_controls+=1
    slices=[]
    for prime in((1<<127)-1,(1<<89)-1):
        base={v:rng.randrange(1,prime)for v in child['variables']}
        direction={v:rng.randrange(1,prime)for v in child['variables']}
        inputs={v:c%prime for v,c in coefficients.items()}
        values=[]
        for t in range(634):
            env=inputs|{v:(base[v]+t*direction[v])%prime for v in child['variables']}
            values.append(evaluate(nodes,env,prime)[child['output']])
        degree=line_degree(values,prime)
        need(degree==568,'full actualsixportlineattainsdegree568')
        slices.append(dict(prime_bits=prime.bit_length(),degree=degree))
    bad=deepcopy(child);target=mapping[42];bad['nodes'][target][2]=mapping[25]
    try:verify_remap(parent,bad,remap)
    except ValueError:pass
    else:raise ValueError('incorrectaliasoperandaccepted')
    bad=deepcopy(parent);bad['nodes'][67]=['add',65,66]
    try:verify_remap(bad,child,remap)
    except ValueError:pass
    else:raise ValueError('incorrectearlierDfdefinitionaccepted')
    for name in('original-review.json','original-review-optimized.json'):
        review=load(HERE/'source'/name)
        need(review['status']=='PASS'and review['equations']['crt14_degree568']['sha256']==PARENT_SHA and
             review['full_scoped_author_replay']['status']=='PASS','full original independentandscopedauthorreceipts')
    for name,pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/name).read_bytes())==pin,'generated artifactseal '+name)
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),integer_variables=14,
        operations=145,operation_counts=dict(counts),exact_degree=568,norm_degree=512,syntactic_bound=632,
        parent_nodes=175,child_nodes=173,complete_alias_remap=True,deleted_parent_nodes=[41,68],
        complete_norm_coefficients=len(norm.t),all_six_norm_cut_ports_bound=True,
        exact_unit_product_finalizer_identity=True,actual_tuple_all_node_controls=diagnostics,
        free_signed_coefficient_all_node_controls=free_controls,actual_tuple_degree_slices=slices,
        corrupted_alias_operand_and_Df_definition_rejected=True,all104archive_members_authenticated=True,
        whole_six_payloads=payloads,parent_equation_sha256=PARENT_SHA,
        equation_sha256=digest((HERE/'equation.json').read_bytes()),
        scope='Exact universal full-polynomial identity by two local cancellations and complete175-to173node map. Authentic six coefficients, independent495-term clearednorm, inherited ordinary proof/degree and supplemental literalcontrols. No Lean or new internal-ZFC/nativecalibration claim.')
    name='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json'
    (HERE/name).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
