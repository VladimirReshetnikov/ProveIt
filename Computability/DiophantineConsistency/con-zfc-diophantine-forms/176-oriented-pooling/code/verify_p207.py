"""Exact, independent verifier for the literal oriented-pooling P207 DAG.

Imports no producer. Uses standard-library integer polynomial arithmetic.
The accompanying independent P216 ports audit supplies separately checked
semantic bindings and the explicit frame/orientation row identities.
"""
from pathlib import Path
from collections import Counter
import argparse
import copy
import hashlib
import json

SOURCE_SHA='a91308bd0c82182ea15080763cb23cb4fa0aa45a812eabb7a6cbcd21c0b95a06'
DROPV={141,142,143,144,145,146,212,213,214,215}
DROPR={97,98,99,100,101,102,149,150,151,152}

def need(v,msg):
    if not v: raise ValueError(msg)
def read(p): return json.loads(p.read_text())
def co(v): return {():v} if v else {}
def va(i): return {(i,):1}
def scale(c,p): return {m:c*v for m,v in p.items() if c*v}
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def mul(p,q,caps=None):
    d={}
    for a,c in p.items():
        for b,e in q.items():
            m=tuple(sorted(a+b))
            if caps is not None and any(v>caps.get(k,0) for k,v in Counter(m).items()):continue
            d[m]=d.get(m,0)+c*e
    return {m:c for m,c in d.items() if c}
def prod(ps):
    p=co(1)
    for q in ps:p=mul(p,q)
    return p
def decode(a,n):
    need(type(a) is list,'sparse terms must be list')
    out={}
    for term in a:
        need(type(term) is list and len(term)==2,'sparse pair')
        c,m=term
        need(type(c) is int and c!=0,'nonzero integer coefficient')
        need(type(m) is list and all(type(i) is int and 0<=i<n for i in m),'coordinate range')
        need(m==sorted(m),'canonical monomial order')
        need(tuple(m) not in out,'duplicate monomial')
        out[tuple(m)]=c
    return out
def rename(p,mp):return {tuple(sorted(mp[i] for i in m)):c for m,c in p.items()}
def same(p,q,msg):need(p==q,msg)

def parse_nodes(doc):
    need(doc.get('domain')=='unrestricted integers','domain')
    need(len(doc.get('variables',[]))==207,'207 variables')
    nodes=doc.get('nodes');need(type(nodes) is list and nodes,'nodes list')
    degrees=[]
    for j,node in enumerate(nodes):
        need(type(node) is list and node,'node list')
        op=node[0]
        if op=='const':
            need(len(node)==2 and type(node[1]) is int,'integer constant')
            degrees.append(0)
        elif op=='var':
            need(len(node)==2 and type(node[1]) is int and 0<=node[1]<207,'var node')
            degrees.append(1)
        elif op in ('add','sub','mul'):
            need(len(node)==3 and all(type(k) is int and 0<=k<j for k in node[1:]),'acyclic binary node')
            degrees.append(degrees[node[1]]+degrees[node[2]] if op=='mul' else max(degrees[node[1]],degrees[node[2]]))
        else:raise ValueError('unsupported polynomial operation')
    root=doc.get('root');need(type(root) is int and 0<=root<len(nodes),'root range')
    return nodes,degrees

def expand(nodes,target,cuts=None,caps=None):
    cuts=cuts or {};pending=[target];wanted=set()
    while pending:
        j=pending.pop()
        if j in wanted:continue
        wanted.add(j)
        if j not in cuts and nodes[j][0] in ('add','sub','mul'):pending.extend(nodes[j][1:])
    out={}
    for j in sorted(wanted):
        if j in cuts:out[j]=cuts[j];continue
        node=nodes[j];op=node[0]
        if op=='const':out[j]=co(node[1])
        elif op=='var':out[j]=va(node[1]) if caps is None or caps.get(node[1],0)>0 else {}
        elif op=='add':out[j]=add(out[node[1]],out[node[2]])
        elif op=='sub':out[j]=add(out[node[1]],scale(-1,out[node[2]]))
        else:out[j]=mul(out[node[1]],out[node[2]],caps)
    return out[target]

def sum_of_squares(nodes,root,residuals):
    # Read the final expression as a sum of literal square nodes; this does
    # not rely on heuristic numerical polynomial-identity testing.
    counts=Counter();pending=[root]
    allowed=set(residuals)
    while pending:
        j=pending.pop();node=nodes[j]
        if node[0]=='add':pending.extend(node[1:])
        elif node[0]=='const' and node[1]==0:pass
        elif node[0]=='mul' and node[1]==node[2] and node[1] in allowed:counts[node[1]]+=1
        else:raise ValueError('root is not the specified literal sum of residual squares')
    need(counts==Counter(residuals),'every specified residual squared exactly once')

def verify(doc,parent,ports,certificate,quadratics):
    nodes,degrees=parse_nodes(doc)
    need(doc.get('source_sha256')==SOURCE_SHA,'source digest in DAG')
    kept=[i for i in range(216) if i not in DROPV];mp={old:new for new,old in enumerate(kept)}
    need(certificate.get('removed_rows')==sorted(DROPR),'deleted rows certificate')
    need(certificate.get('removed_variables')==sorted(DROPV),'deleted variables certificate')
    need(certificate.get('old_to_new')==[[i,mp[i]] for i in kept],'coordinate deletion map')
    need(certificate.get('source_sha256')==SOURCE_SHA,'certificate source digest')
    need(doc['variables'][:206]==[dict(parent['variables'][i],source_index=i) for i in kept],'retained coordinate order and metadata')
    rows=[decode(r['terms'],216) for r in parent['residuals']]
    need({j for j,p in enumerate(rows) if DROPV & {i for m in p for i in m}}==DROPR,'private support isolation')
    retained=[j for j in range(153) if j not in DROPR]
    residuals=doc.get('residual_nodes');need(type(residuals) is list and len(residuals)==144,'144 residual roots')
    need(all(type(j) is int and 0<=j<len(nodes) for j in residuals),'residual root ranges')
    need(len(set(residuals))==144,'distinct residual roots')
    need(len(quadratics)==143,'quadratic list length')
    for ordinal,j in enumerate(retained):
        expected=rename(rows[j],mp)
        same(expand(nodes,residuals[ordinal]),expected,'retained residual '+str(j))
        q=quadratics[ordinal]
        need(q['parent_row']==j and q['label']==parent['residuals'][j]['label'],'quadratic provenance')
        same(decode(q['terms'],207),expected,'printed sparse quadratic '+str(j))
        need(degrees[residuals[ordinal]]<=2,'quadratic degree')

    ids=doc.get('ports_node_ids');need(type(ids) is dict,'port node map')
    all_port_refs=[ids['A'],ids['reciprocal']]
    for key in ['bases','T','H','S','E']:all_port_refs.extend(ids[key])
    need(all(type(j) is int and 0<=j<len(nodes) for j in all_port_refs),'port node reference ranges')
    need(ids['reciprocal']==residuals[-1],'new residual node')
    same(expand(nodes,ids['A']),rename(decode(ports['A'],216),mp),'A port')
    for key in ['bases','T','H','S','E']:need(len(ids[key])==5,'five blocks '+key)
    for j,group in enumerate(ports['groups']):
        for key,source in [('bases','base'),('T','T'),('H','H'),('S','S'),('E','E')]:
            same(expand(nodes,ids[key][j]),rename(decode(group[source],216),mp),'block '+str(j)+' '+key)
    byid={r['request']:r for r in ports['requests']}
    claimed=certificate['ports']
    same(decode(claimed['A'],216),decode(ports['A'],216),'certificate A')
    need(len(claimed['requests'])==17,'17 claimed requests')
    need([r['number'] for r in claimed['requests']]==list(byid),'request order')
    for r in claimed['requests']:
        ref=byid[r['number']]
        for key,target in [('m','output'),('k','index'),('D','D'),('Y','Y'),('Z','Z')]:
            same(decode(r[key],216),decode(ref[target],216),'certificate request '+str(r['number'])+' '+key)
        need(r['number'] in ports['groups'][r['group']]['requests'],'correct base grouping')

    # Independently expand only the six-term expression in abstract N,T,E
    # ports after proving each substituted port polynomial above.
    cuts={}
    for j in range(5):
        for key,index in [('bases',j),('T',5+j),('E',10+j)]:
            node=ids[key][j]
            need(node not in cuts,'distinct abstract cuts')
            cuts[node]=va(index)
    z_nodes=[j for j,node in enumerate(nodes) if node==['var',206]]
    need(len(z_nodes)==1,'unique final variable leaf')
    cuts[z_nodes[0]]=va(15)
    expected=add(*(prod([va(j),va(10+j)]+[va(5+k) for k in range(5) if k!=j]) for j in range(5)),scale(-1,prod([va(15)]+[va(5+k) for k in range(5)])))
    same(expand(nodes,residuals[-1],cuts),expected,'oriented all-base residual exact identity')
    sum_of_squares(nodes,doc['root'],residuals)

    # A target coefficient is computed in the quotient ring killing all
    # other variables and exponents above this monomial. No sampling.
    caps={0:2,4:2,94:4,130:1,178:1,180:2}
    target=tuple(i for i,c in sorted(caps.items()) for _ in range(c))
    coefficient=expand(nodes,residuals[-1],caps=caps).get(target,0)
    need(coefficient==-2 and len(target)==12,'nonzero degree-12 residual coefficient')
    need(degrees[residuals[-1]]==12 and degrees[doc['root']]==24,'upper degree bounds')
    dc=doc['exact_degree_certificate']
    need(dc['monomial']==[[i,c] for i,c in sorted(caps.items())] and dc['coefficient']==-2 and dc['degree']==24 and dc['residual_degree']==12,'declared degree certificate')
    live=set();pending=[doc['root']]
    while pending:
        j=pending.pop()
        if j in live:continue
        live.add(j)
        if nodes[j][0] in ('add','sub','mul'):pending.extend(nodes[j][1:])
    used={nodes[j][1] for j in live if nodes[j][0]=='var'}
    need(used==set(range(207)),'all 207 declared variables used')
    return {'status':'passed','variables':207,'retained_quadratics':143,'total_residuals':144,
            'exact_degree':24,'degree12_residual_coefficient':coefficient,
            'live_nodes':len(live),'binary_operations':sum(nodes[j][0] in ('add','sub','mul') for j in live)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--package',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--ports',type=Path)
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args();root=args.package
    parent_path=root/'source/equation216.json'
    need(hashlib.sha256(parent_path.read_bytes()).hexdigest()==SOURCE_SHA,'literal parent file digest')
    parent=read(parent_path)
    ports=read(args.ports or root/'verification/P216_PORTS_AUDIT.json')
    need(ports['parent_sha256']==SOURCE_SHA and ports['status']=='passed','independent port audit identity')
    doc=read(root/'equations/P207.json')
    certificate=read(root/'equations/P207_certificate.json')
    quadratics=read(root/'equations/P207_quadratic_rows.json')
    result=verify(doc,parent,ports,certificate,quadratics)
    controls=[]
    mutations=[('noninteger constant',lambda d:d['nodes'].__setitem__(0,['const',True])),
               ('changed A port',lambda d:d['ports_node_ids'].__setitem__('A',d['ports_node_ids']['bases'][0])),
               ('wrong retained residual',lambda d:d['residual_nodes'].__setitem__(0,d['residual_nodes'][1])),
               ('missing global pool square',lambda d:d.__setitem__('root',d['nodes'][d['root']][1])),
               ('false leading coefficient',lambda d:d['exact_degree_certificate'].__setitem__('coefficient',2))]
    for label,mutation in mutations:
        bad=copy.deepcopy(doc);mutation(bad)
        try:verify(bad,parent,ports,certificate,quadratics)
        except (ValueError,KeyError,IndexError,TypeError):controls.append(label)
        else:raise ValueError('corruption accepted: '+label)
    result['negative_controls_rejected']=controls
    result['scope']='Exact finite source/port/DAG identities; unbounded soundness and completeness are the ordinary mathematical proof.'
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
