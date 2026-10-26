#!/usr/bin/env python3
"""Fuse the index-orientation certificate with selected power certificates."""
from build_pool import ROOT,DAG,build,ports,save,analyze
import json

def make_joint(parent,group_index=None):
    removed=next(i for i,v in enumerate(parent['variables']) if v['source_index']==201)
    keep=[i for i in range(len(parent['variables'])) if i!=removed]
    ren={i:j for j,i in enumerate(keep)}
    d=DAG(); nodes=parent['nodes'];translated={}
    def copy(j):
        if j in translated:return translated[j]
        node=nodes[j]
        if node[0]=='const':n=d.c(node[1])
        elif node[0]=='var':
            if node[1]==removed:raise ValueError('orientation quotient escapes its private row')
            n=d.v(ren[node[1]])
        else:
            n=getattr(d,node[0])(copy(node[1]),copy(node[2]))
        translated[j]=n;return n
    residuals=[];info=[]
    target_ordinal=len(parent['residual_nodes'])-1 if group_index is None else 143+group_index
    for ordinal,(r,meta) in enumerate(zip(parent['residual_nodes'],parent['residual_info'])):
        if meta['parent_row']==142:continue
        residuals.append(copy(r));info.append(meta)
    target_position=next(i for i,m in enumerate(info) if m==parent['residual_info'][target_ordinal])
    original_to_new={v['source_index']:ren[i] for i,v in enumerate(parent['variables']) if i!=removed and v['source_index'] is not None}
    p=ports();poly=lambda ts:d.polynomial(ts,original_to_new)
    unique=[];seen=set()
    for r in p['requests']:
        key=json.dumps([r['D'],r['Y'],r['Z']])
        if key in seen:continue
        seen.add(key);unique.append(r)
    omega=d.sum(d.add(d.square(d.sub(d.add(poly(r['D']),poly(r['Z'])),d.c(1))),
                      d.square(d.sub(poly(r['Y']),poly(r['k'])))) for r in unique)
    denominator=d.sub(poly(p['A']),d.c(1))
    group=list(range(5)) if group_index is None else parent['partition'][group_index]
    product=d.product(copy(parent['ports_node_ids']['T'][j]) for j in group)
    old_pool=copy(parent['residual_nodes'][target_ordinal])
    joint=d.add(d.mul(omega,product),d.mul(denominator,old_pool))
    residuals[target_position]=joint
    info[target_position]=dict(parent_row=None,label='joint_orientation_and_power_pool')
    root=d.sum(d.square(r) for r in residuals)
    doc=dict(schema='conzfc.integer-polynomial-dag.v1',domain='unrestricted integers',
             variables=[parent['variables'][i] for i in keep],nodes=d.nodes,
             residual_nodes=residuals,residual_info=info,root=root,
             source_sha256=parent['source_sha256'],source_commit=parent['source_commit'],
             fusion=dict(deleted_source_variable=201,deleted_source_row=142,
                         fused_group=group,orientation_requests=[r['number'] for r in unique],
                         omega_node=omega,index_denominator_node=denominator,
                         power_denominator_product_node=product,old_pool_node=old_pool,
                         joint_node=joint),
             ports_node_ids={key:[copy(j) for j in vals] for key,vals in parent['ports_node_ids'].items() if key in ['bases','T','H','S','E']})
    # The port lists introduce no new nodes: every port is already live.
    doc['ports_node_ids']['A']=poly(p['A'])
    cert=dict(schema='conzfc.joint-orientation-pooling.v1',
              source_variable_deletion=201,source_row_deletion=142,
              parent_to_new=[[i,ren[i]] for i in keep],
              fused_group=group,unique_requests=[r['number'] for r in unique])
    if group_index is None:
        monomial=[(0,2),(4,2),(94,4),(130,1),(134,1),(184,1),(186,2)]
        doc['exact_degree_certificate']=dict(degree=26,residual_degree=13,coefficient=-2,
                    source_monomial=[list(x) for x in monomial],
                    monomial=[[original_to_new[v],e] for v,e in monomial])
    return doc,cert

def main():
    parent,_,_=build()
    joint,certificate=make_joint(parent)
    save(ROOT/'equations/P206_joint.json',joint)
    save(ROOT/'equations/P206_joint_certificate.json',certificate)
    m=analyze(joint);m['degree']=26
    save(ROOT/'equations/P206_joint_metrics.json',m)
    result={'P206_joint':m}
    parent,_,_=build([[0],[1],[2],[3],[4]])
    joint,certificate=make_joint(parent,0)
    save(ROOT/'equations/partitions/P210_joint.json',joint)
    save(ROOT/'equations/partitions/P210_joint_certificate.json',certificate)
    result['P210_joint']=analyze(joint)
    save(ROOT/'equations/partitions/P210_joint_metrics.json',result['P210_joint'])
    parent,_,_=build([[0],[1,2],[3,4]])
    joint,certificate=make_joint(parent,0)
    save(ROOT/'equations/partitions/P208_joint.json',joint)
    save(ROOT/'equations/partitions/P208_joint_certificate.json',certificate)
    result['P208_joint']=analyze(joint)
    save(ROOT/'equations/partitions/P208_joint_metrics.json',result['P208_joint'])
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
