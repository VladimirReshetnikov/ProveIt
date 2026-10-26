"""Exact, independent verifier for oriented-pooling and joint-pooling DAGs.

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

def parse_nodes(doc, nvar):
    need(doc.get('domain')=='unrestricted integers','domain')
    need(len(doc.get('variables',[]))==nvar,'variable count')
    nodes=doc.get('nodes');need(type(nodes) is list and nodes,'nodes list')
    degrees=[]
    for j,node in enumerate(nodes):
        need(type(node) is list and node,'node list')
        op=node[0]
        if op=='const':
            need(len(node)==2 and type(node[1]) is int,'integer constant')
            degrees.append(0)
        elif op=='var':
            need(len(node)==2 and type(node[1]) is int and 0<=node[1]<nvar,'var node')
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

# Explicit approved profiles, rather than trusting a producer's partition.
# Tuple: groups, fusion, additional unweighted multi-block groups, exactdegree,
# raw-P216 leading monomial, its expected coefficient.
PROFILES={
 'P206_joint.json':([[0,1,2,3,4]],True,[],26,{0:2,4:2,94:4,130:1,134:1,184:1,186:2},-2),
 'P207.json':([[0,1,2,3,4]],False,[],24,{0:2,4:2,94:4,130:1,184:1,186:2},-2),
 'partitions/P208.json':([[0,1,2],[3,4]],False,[],16,{0:2,4:2,3:1,139:1,186:2},-2),
 'partitions/P209.json':([[0],[1,2],[3,4]],False,[],12,{94:4,130:1,184:1},2),
 'partitions/P210.json':([[0],[1],[2],[3,4]],False,[],12,{94:4,130:1,184:1},2),
 'partitions/P211.json':([[0],[1],[2],[3],[4]],False,[],6,{94:1,130:1,184:1},-2),
 'partitions/P210_consecutive.json':([[0],[1],[2],[3,4]],False,[3],10,{94:3,130:1,184:1},2),
 'partitions/P208_joint.json':([[0],[1,2],[3,4]],True,[],12,{94:4,130:1,184:1},2),
 'partitions/P210_joint.json':([[0],[1],[2],[3],[4]],True,[],8,{0:2,183:2},-1),
}

def verify_profile(name,doc,parent,ports):
    groups,fused,unweighted,degree,rawcaps,target_coefficient=PROFILES[name]
    dropv=DROPV|({201} if fused else set())
    dropr=DROPR|({142} if fused else set())
    retainedv=[i for i in range(216) if i not in dropv]
    retainedr=[i for i in range(153) if i not in dropr]
    mp={old:new for new,old in enumerate(retainedv)}
    nsource=len(retainedv);nvar=nsource+len(groups)
    nodes,degrees=parse_nodes(doc,nvar)
    need(doc['source_sha256']==SOURCE_SHA,'source digest')
    need(doc['variables'][:nsource]==[dict(parent['variables'][i],source_index=i) for i in retainedv],'exact retained variable order')
    need(all(v.get('kind')=='oriented_pool' and v.get('source_index') is None for v in doc['variables'][nsource:]),'new integer quotient variables')
    rows=[decode(r['terms'],216) for r in parent['residuals']]
    need({j for j,p in enumerate(rows) if dropv & {i for m in p for i in m}}==dropr,'private-coordinate isolation')
    residuals=doc['residual_nodes']
    need(len(residuals)==len(retainedr)+len(groups),'residual count')
    need(len(set(residuals))==len(residuals),'distinct residual node IDs')
    need(all(type(j) is int and 0<=j<len(nodes) for j in residuals),'valid residual node IDs')
    info=doc['residual_info'];need(len(info)==len(residuals),'residual info count')
    for ordinal,j in enumerate(retainedr):
        same(expand(nodes,residuals[ordinal]),rename(rows[j],mp),'retained row '+str(j))
        need(info[ordinal]['parent_row']==j and info[ordinal]['label']==parent['residuals'][j]['label'],'retained row provenance')
        need(degrees[residuals[ordinal]]<=2,'retained row quadratic')
    pool_roots=residuals[len(retainedr):]
    ids=doc['ports_node_ids']
    all_port_refs=[ids['A']]
    for key in ['bases','T','H','S','E']:all_port_refs.extend(ids[key])
    need(all(type(j) is int and 0<=j<len(nodes) for j in all_port_refs),'port node reference ranges')
    same(expand(nodes,ids['A']),rename(decode(ports['A'],216),mp),'signed center A')
    for key in ['bases','T','H','S','E']:need(len(ids[key])==5,'five '+key+' ports')
    for j,group in enumerate(ports['groups']):
        for key,source in [('bases','base'),('T','T'),('H','H'),('S','S'),('E','E')]:
            same(expand(nodes,ids[key][j]),rename(decode(group[source],216),mp),'literal '+key+' block '+str(j))

    cuts={}
    for j in range(5):
        for key,index in [('bases',j),('T',5+j),('E',10+j)]:
            node=ids[key][j];need(node not in cuts,'distinct semantic cut nodes');cuts[node]=va(index)
    for q in range(len(groups)):
        matches=[j for j,node in enumerate(nodes) if node==['var',nsource+q]]
        need(len(matches)==1,'unique quotient leaf');cuts[matches[0]]=va(15+q)
    expected_pools=[]
    for q,group in enumerate(groups):
        terms=[]
        for j in group:
            factors=[va(10+j)]+[va(5+k) for k in group if k!=j]
            # Existing singleton residuals intentionally use no n factor.
            if len(group)>1 and q not in unweighted:factors.insert(0,va(j))
            terms.append(prod(factors))
        expected_pools.append(add(*terms,scale(-1,prod([va(15+q)]+[va(5+k) for k in group]))))
    if not fused:
        if name!='P207.json':need(doc.get('partition')==groups,'literal declared partition')
        roots=ids['reciprocal'];roots=[roots] if type(roots) is int else roots
        need(roots==pool_roots,'pool root references')
        for q,root in enumerate(pool_roots):
            same(expand(nodes,root,cuts),expected_pools[q],'entire pool residual '+str(q))
    else:
        fusion=doc['fusion']
        need(all(type(fusion[k]) is int and 0<=fusion[k]<len(nodes) for k in ['joint_node','old_pool_node','omega_node','index_denominator_node','power_denominator_product_node']),'fusion node reference ranges')
        need(fusion['deleted_source_row']==142 and fusion['deleted_source_variable']==201,'orientation slot removal')
        need(fusion['fused_group']==groups[0],'correct fused group')
        need(fusion['joint_node']==pool_roots[0],'joint root reference')
        # Omega is reconstructed from14 unique raw pairs and exact intended
        # indices; no canonical orientation premise is used here.
        bypair={}
        for r in ports['requests']:bypair[r['pair']]=r
        need(len(bypair)==14,'14 raw pairs')
        omega={}
        for r in bypair.values():
            X=rename(decode(r['X'],216),mp);Y=rename(decode(r['Y'],216),mp)
            k=rename(decode(r['index'],216),mp)
            omega=add(omega,mul(add(X,co(-1)),add(X,co(-1))),mul(add(Y,scale(-1,k)),add(Y,scale(-1,k))))
        same(expand(nodes,fusion['omega_node']),omega,'entire raw orientation sum')
        same(expand(nodes,fusion['index_denominator_node']),va(mp[134]),'A-1 orientation denominator')
        same(expand(nodes,fusion['power_denominator_product_node'],cuts),prod([va(5+k) for k in groups[0]]),'fused denominator product')
        same(expand(nodes,fusion['old_pool_node'],cuts),expected_pools[0],'complete fused old-power residual')
        jointcuts=dict(cuts)
        jointcuts[fusion['omega_node']]=va(30)
        jointcuts[fusion['index_denominator_node']]=va(31)
        expected=add(mul(va(30),prod([va(5+k) for k in groups[0]])),mul(va(31),expected_pools[0]))
        same(expand(nodes,pool_roots[0],jointcuts),expected,'complete fused orientation/power expression')
        for q,root in enumerate(pool_roots[1:],1):
            same(expand(nodes,root,cuts),expected_pools[q],'remaining partition residual '+str(q))

    sum_of_squares(nodes,doc['root'],residuals)
    need(degrees[doc['root']]==degree,'degree upper bound')
    caps={mp[i]:c for i,c in rawcaps.items()}
    monomial=tuple(i for i,c in sorted(caps.items()) for _ in range(c))
    candidates=[r for r in pool_roots if degrees[r]==degree//2]
    computed=[expand(nodes,r,caps=caps).get(monomial,0) for r in candidates]
    need(target_coefficient in computed,'exact nonzero top-degree residual coefficient')
    need(len(monomial)==degree//2,'target homogeneous degree')
    if 'exact_degree_certificate'in doc:
        dc=doc['exact_degree_certificate']
        need(dc['degree']==degree and dc['residual_degree']==degree//2 and dc['coefficient']==target_coefficient,'claimed degree certificate')
        need(dc['monomial']==[[i,c] for i,c in sorted(caps.items())],'claimed degree monomial')
    live=set();pending=[doc['root']]
    while pending:
        j=pending.pop()
        if j in live:continue
        live.add(j)
        if nodes[j][0] in ('add','sub','mul'):pending.extend(nodes[j][1:])
    used={nodes[j][1] for j in live if nodes[j][0]=='var'}
    need(used==set(range(nvar)),'all declared coordinates used')
    return {'file':name,'status':'passed','variables':nvar,'retained_quadratics':len(retainedr),
            'residuals':len(residuals),'exact_degree':degree,'leading_residual_monomial':[[i,c] for i,c in sorted(caps.items())],
            'leading_residual_coefficient':target_coefficient,'live_nodes':len(live),
            'binary_operations':sum(nodes[j][0] in ('add','sub','mul') for j in live)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--package',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--ports',type=Path)
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--profile',action='append',choices=list(PROFILES))
    args=parser.parse_args();root=args.package
    parentpath=root/'source/equation216.json'
    need(hashlib.sha256(parentpath.read_bytes()).hexdigest()==SOURCE_SHA,'literal parent hash')
    parent=read(parentpath);ports=read(args.ports or root/'verification/P216_PORTS_AUDIT.json')
    need(ports['parent_sha256']==SOURCE_SHA and ports['status']=='passed','port audit source identity')
    # The independently checked raw anchor is necessary for every fused
    # profile and the frame combination must omit the removed orientation row.
    need(len(ports['raw_anchor_before_orientation'])==14,'raw anchor audit available')
    need(all(142 not in [row for c,row in e['final_row_combination']] for e in ports['raw_anchor_before_orientation'].values()),'no orientation row in raw anchor')
    need(142 not in [row for c,row in ports['frame_final_row_combination']],'frame independent of orientation')
    results=[];controls=[]
    for name in args.profile or list(PROFILES):
        doc=read(root/'equations'/name)
        results.append(verify_profile(name,doc,parent,ports))
        # Corrupt the actual center binding in every profile; normal and
        # optimized Python must both reject the same concrete corruption.
        bad=copy.deepcopy(doc);bad['ports_node_ids']['A']=bad['ports_node_ids']['bases'][0]
        try:verify_profile(name,bad,parent,ports)
        except (ValueError,KeyError,IndexError,TypeError):controls.append(name+': altered A port rejected')
        else:raise ValueError('corruption passed '+name)
    out={'status':'passed','profiles':results,'negative_controls_rejected':controls,
         'scope':'Exact literal source/port/DAG identities and degree certificates. Raw cap and unbounded mathematical lemmas are identified separately.'}
    if args.receipt:args.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
