#!/usr/bin/env python3
"""Exact four-cut ring identity, every retained register, full fixed values."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
REPO=RESEARCH.parents[1]
ARCHIVE=REPO/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
ARCHIVE_SHA='37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0'
BASE='ConZFC_Constructive_Reductions_2026-10-23/nine/'
OPS={'add','sub','mul'}
CASES=[dict(name='boundary_simple',operations=420,degree=1472168,profile='boundary',
            parent_sha256='ea0804c38989d9c5bedeca04a9dced04d4daeb1b3cc79176e3f0580b76f83528'),
       dict(name='boundary_complete',operations=1057,degree=997810,profile='boundary',
            parent_sha256='3f5f4f92feebd9bd1392af21e3faccf674f1d1e96ac2637cc22a22c73fcfc3bc'),
       dict(name='compact_simple',operations=428,degree=1626248,profile='compact',
            parent_sha256='293c17f01ef5e7bb7dd3795f9d3261eebac6bf2b88d2a76048ab8f378e70e141')]


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def load_archive():
    need(digest(ARCHIVE.read_bytes())==ARCHIVE_SHA,'whole immutable archive')
    return zipfile.ZipFile(ARCHIVE)


def fixed_values(z,profile,parent):
    """Neither compression format nor modular hashes stand in for value equality."""
    earlier=RESEARCH/('candidates/saturated-h1868-d/source/data'if profile=='boundary'else
                     'candidates/split116-compact/compact54-sharp/coefficients/compact_tuple')
    sub=''if profile=='boundary'else'compact/'
    ports={};records=[]
    for name in ('beta','K','MC','MF_source'):
        raw=gzip.decompress(z.read(BASE+sub+'data/'+name+'.bin.gz'))
        prior=gzip.decompress((earlier/(name+'.bin.gz')).read_bytes())
        need(raw==prior,'whole earlier port '+profile+'/'+name)
        ports[name]=int.from_bytes(raw,'little')
        records.append(dict(name=name,raw_bytes=len(raw),raw_sha256=digest(raw)))
    ordered=[ports[n]for n in ('beta','K','MC','MF_source')]
    expected={'base_scale':1<<parent['base_scale_exponent'],
              'threshold_scale':1<<parent['threshold_scale_exponent']}
    for name,terms in parent['coefficient_recipes'].items():
        expected[name]=sum(t['coefficient']*product([x**e for x,e in zip(ordered,t['powers'])])for t in terms)
    binding=json.loads(z.read(BASE+'fixed/'+profile+'/BINDING.json'));actual={};payloads=[]
    for r in binding['records']:
        compressed=z.read(BASE+r['path']);raw=gzip.decompress(compressed)
        need(digest(compressed)==r['gzip_sha256']and digest(raw)==r['raw_sha256'],'entire fixed payload hashes')
        need(r['sign']in(-1,1),'external sign')
        value=r['sign']*int.from_bytes(raw,'little')
        need(value.bit_length()==r['bits']and value==expected[r['name']],'exact fixed integer recipe '+r['name'])
        need(r['name']not in actual,'unique fixed leaf');actual[r['name']]=value
        payloads.append(dict(name=r['name'],sign=r['sign'],bits=r['bits'],raw_bytes=len(raw),
                             raw_sha256=digest(raw),gzip_sha256=digest(compressed)))
    need(set(actual)==set(expected)=={n['name']for n in parent['nodes']if n['kind']=='fixed'},'all fixed leaves')
    return actual,dict(profile=profile,whole_ports=records,fixed_leaves=payloads,
                       binding_member=BASE+'fixed/'+profile+'/BINDING.json',
                       binding_sha256=digest(z.read(BASE+'fixed/'+profile+'/BINDING.json')))


def product(xs):
    out=1
    for x in xs:out*=x
    return out


def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if not out[m]:del out[m]
    return out


def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return{m:c for m,c in out.items()if c}


def normal_form(graph,cuts):
    memo={};visited=set()
    def visit(i):
        need(type(i)is int and 0<=i<len(graph['nodes']),'tail node range')
        if i in cuts:return{(cuts[i],):1}
        visited.add(i)
        if i not in memo:
            n=graph['nodes'][i];kind=n['kind']
            if kind=='literal':memo[i]={():n['value']}if n['value']else{}
            else:
                need(kind in OPS,'unexpected leaf outside complete norm cut')
                a,b=visit(n['left']),visit(n['right'])
                memo[i]=mul(a,b)if kind=='mul'else add(a,b,-1 if kind=='sub'else 1)
        return memo[i]
    return visit(graph['output']),visited


def graph_check(graph,expected_ops):
    nodes=graph['nodes'];counts=Counter()
    for i,n in enumerate(nodes):
        need(n['kind']in OPS|{'variable','fixed','literal'},'known node kind')
        if n['kind']in OPS:
            need(all(type(n[j])is int and 0<=n[j]<i for j in('left','right')),'strict topological ordering');counts[n['kind']]+=1
    live=set();todo=[graph['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        need(0<=i<len(nodes),'live range');live.add(i);n=nodes[i]
        if n['kind']in OPS:todo.extend((n['left'],n['right']))
    need(live==set(range(len(nodes))),'all nodes live')
    need(sum(counts.values())==expected_ops==graph['total_operations'],'literal live operation count')
    need(dict(sorted(counts.items()))==graph['operation_counts'],'operation kinds')
    need(graph['domain']=='strictly positive integers'and len(graph['variables'])==9,'nine positive domain')
    need(sorted(n['name']for n in nodes if n['kind']=='variable')==sorted(graph['variables']),'all nine input leaves once')
    return dict(nodes=len(nodes),operations=sum(counts.values()),operation_counts=dict(counts),all_nodes_live=True)


def verify_identity(parent,child,cert,case):
    before=graph_check(parent,case['operations']);after=graph_check(child,case['operations']-1)
    mapping={int(i):j for i,j in cert['retained_remap'].items()};cut=cert['cutset']
    need(len(cut)==4 and len(set(cut))==4 and set(cut)<=set(mapping),'four distinct mapped cut coordinates')
    old,old_tail=normal_form(parent,{i:k for k,i in enumerate(cut)})
    new,new_tail=normal_form(child,{mapping[i]:k for k,i in enumerate(cut)})
    # Expand the entire t,s,a,b polynomial independently of both circuit tails.
    t,s,a,b=[{(i,):1}for i in range(4)]
    squared=mul(t,t);norm=add(squared,mul(s,add(a,b)),-1)
    expected=add(mul(norm,norm),mul({():4},mul(mul(s,s),mul(a,b))),-1)
    need(old==new==expected and len(expected)==6,'complete exact six-term ring identity')
    covered=set(new_tail)
    for i,j in mapping.items():
        need(0<=i<len(parent['nodes'])and 0<=j<len(child['nodes']),'prefix remap range')
        node=dict(parent['nodes'][i])
        if node['kind']in OPS:
            need(node['left']in mapping and node['right']in mapping,'every prefix operand mapped')
            node.update(left=mapping[node['left']],right=mapping[node['right']])
            if node['kind']in('add','mul')and node['left']>node['right']:node['left'],node['right']=node['right'],node['left']
        need(node==child['nodes'][j],'every complete retained node identity');covered.add(j)
    need(covered==set(range(len(child['nodes']))),'every child node justified by prefix or exact norm')
    for key in ('variables','domain','coefficient_recipes','coherent_tuple','profile','source_snapshot',
                'base_scale_exponent','threshold_scale_exponent','source_degree','threshold_degree'):
        need(parent[key]==child[key],'unchanged whole scalar source binding '+key)
    need(parent['exact_degree']==child['exact_degree']==case['degree'],'same exact degree metadata')
    return dict(before=before,after=after,complete_prefix_nodes=len(mapping),exact_tail_monomials=6,
                degree_identity='Exact equality of the entire polynomial transfers the accepted parent exact degree; no syntactic upper bound is substituted.')


def evaluate(graph,variables,fixed,p):
    out=[]
    for n in graph['nodes']:
        k=n['kind']
        if k=='variable':v=variables[n['name']]
        elif k=='fixed':v=fixed[n['name']]
        elif k=='literal':v=n['value']
        else:
            a,b=out[n['left']],out[n['right']]
            v=a*b if k=='mul'else a-b if k=='sub'else a+b
        out.append(v%p)
    return out


def run():
    results=[];pins={}
    source=json.loads((HERE/'SOURCE_PINS.json').read_text());build=json.loads((HERE/'BUILD.json').read_text())
    need(source['archive_sha256']==ARCHIVE_SHA and source['parents']==CASES,'complete source pins')
    need(digest((RESEARCH/source['prior_ordinary_review']).read_bytes())==source['prior_review_sha256'],'accepted ordinary review pin')
    need(digest(Path(__file__).read_bytes())==build['independent_checker_sha256'],'independent checker binding')
    for name,h in build['sha256'].items():need(digest((HERE/name).read_bytes())==h,'all generated file bytes '+name)
    with load_archive()as z:
        for name,h in source['required_inherited_proof_members'].items():need(digest(z.read(BASE+name))==h,'exact inherited proof/member '+name)
        for case in CASES:
            name=case['name'];member=BASE+'equations/'+name+'.json';raw=z.read(member)
            need(digest(raw)==case['parent_sha256'],'exact parent graph bytes')
            parent=json.loads(raw);child=json.loads((HERE/(name+'.json')).read_text())
            cert=json.loads((HERE/(name+'_identity.json')).read_text())
            need(cert['parent_sha256']==digest(raw)and cert['child_sha256']==digest((HERE/(name+'.json')).read_bytes()),'exact graph bindings')
            fixed,pin=fixed_values(z,case['profile'],parent);pins[case['profile']]=pin
            receipt=verify_identity(parent,child,cert,case)
            for p in(65537,1000000007,2147483647):
                for seed in range(20):
                    values={n:seed*(j+3)-17 for j,n in enumerate(child['variables'])}
                    old,new=evaluate(parent,values,fixed,p),evaluate(child,values,fixed,p)
                    need(old[parent['output']]==new[child['output']],'actual integer fixed-value diagnostic')
                    need(all(old[int(i)]==new[j]for i,j in cert['retained_remap'].items()),'every actual prefix register diagnostic')
            corruptions=[]
            def reject(bad,c,label):
                try:verify_identity(parent,bad,c,case)
                except(ValueError,KeyError,IndexError):corruptions.append(label);return
                raise ValueError('corruption accepted '+label)
            bad=deepcopy(child);out=bad['nodes'][bad['output']];out['left'],out['right']=out['right'],out['left'];reject(bad,cert,'wrong final subtraction orientation')
            bad=deepcopy(child);i=next(i for i,n in enumerate(bad['nodes'])if n['kind']=='fixed');bad['nodes'][i]['name']='wrong_fixed';reject(bad,cert,'altered retained fixed leaf')
            wrong=deepcopy(cert);wrong['retained_remap'][str(cert['cutset'][0])]=wrong['retained_remap'][str(cert['cutset'][1])];reject(child,wrong,'corrupted cut correspondence')
            results.append(dict(name=name,variables=9,domain=child['domain'],operations=child['total_operations'],
                exact_degree=case['degree'],literal_identity=receipt,whole_fixed_leaves=len(fixed),actual_coefficient_assignments=60,
                rejected_corruptions=corruptions))
    need(json.loads((HERE/'FIXED_BINDINGS.json').read_text())==pins,'complete fixed binding report')
    return dict(status='PASS',optimized_python=bool(sys.flags.optimize),archive_sha256=ARCHIVE_SHA,cases=results,
                scope='Complete exact ring identity and every retained prefix node; whole ports and fixed integers bound to the accepted parents. Ordinary native/refutation proofs inherited; no Lean/internal-ZFC claim.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    result=run();text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
