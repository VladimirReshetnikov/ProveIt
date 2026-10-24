#!/usr/bin/env python3
"""Save two universal prefix products in the signed degree312 endpoint."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/constructive-integer14-quadratic'
OUT=ROOT/'candidates/constructive-integer14-quadratic-shared'
PARENT_SHA='738c7adb164ecc7267bee75868f5ab49a9ce9c951684fd8761e0e0f790477828'


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()


def encoded(value):return(json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def build():
    raw=(PARENT/'equation.json').read_bytes()
    need(digest(raw)==PARENT_SHA,'completefrozen121parent')
    parent=json.loads(raw);old=parent['nodes'];nm=parent['named_registers']
    q=nm['q'];M=nm['M'];twice_q=old[M][2]
    q2=next(i for i,row in enumerate(old)if row==['mul',q,q])
    one=next(i for i,row in enumerate(old)if row==['integer',1])
    two=next(i for i,row in enumerate(old)if row==['integer',2])
    need(old[M]==['mul',q,twice_q]and old[twice_q]==['mul',q,two]and q2<M,
         'exactq*(2q)reusecut')
    product=old[nm['Dtau']][2]
    ellprod,k2=old[product][1:]
    ell,ellp=old[ellprod][1:]
    k=nm['k']
    need(old[nm['Dtau']]==['add',one,product]and old[ellp]==['add',one,ell]and
         old[k2]==['mul',k,k]and old[product]==['mul',ellprod,k2], 'exactfirstPellfactorizationcut')
    removed={twice_q,ellp,ellprod,k2}
    need(not removed.intersection(nm.values()),'onlyunnamedprivateintermediatesremoved')
    nodes=[];mapping={};records=[];inserted=[]
    for i,row in enumerate(old):
        if i in removed:
            records.append(dict(parent=i,status='removed_private',old_row=row))
            continue
        if i==product:
            L=len(nodes);nodes.append(['mul',mapping[ell],mapping[k]])
            Lp=len(nodes);nodes.append(['add',L,mapping[k]])
            inserted=[L,Lp]
            new_row=['mul',L,Lp]
        elif i==M:
            new_row=['mul',mapping[two],mapping[q2]]
        else:
            new_row=([row[0],mapping[row[1]],mapping[row[2]]]
                     if row[0]in('add','sub','mul')else deepcopy(row))
        mapping[i]=len(nodes);nodes.append(new_row)
        records.append(dict(parent=i,child=mapping[i],status='retained',
                            changed_cut_definition=i in(product,M)))
    child=deepcopy(parent)
    child.update(name='crt14_quadratic_projection_shared_degree312',nodes=nodes,
        output=mapping[parent['output']],named_registers={k:mapping[i]for k,i in nm.items()},
        parent_sha256=PARENT_SHA,proof='README.md',
        proof_status='Exact universal complete-polynomial identity with the121-operation degree312 parent via two prefix cuts and a complete node map. Ordinary signed proof unchanged; no new Lean/native/internal-ZFC proof.')
    counts=dict(Counter(r[0]for r in nodes if r[0]in('add','sub','mul')))
    child['operation_counts']=counts;child['operations']=sum(counts.values())
    need(len(nodes)==146 and child['operations']==119 and counts=={'mul':68,'add':26,'sub':25},
         'actual119-operation146-nodegraph')
    files={'equation.json':encoded(child),'source/parent-equation.json':raw}
    for target,source in(
        ('source/parent-proof.md','README.md'),('source/ordinary-proof.md','PROOF.md'),
        ('source/parent-check.json','CHECK.json'),('source/parent-check-optimized.json','CHECK_OPTIMIZED.json'),
        ('source/parent-provenance.json','PROVENANCE.json'),
        ('source/proof-peer.md','source/proof-peer.md'),('source/proof-peer.json','source/proof-peer.json'),
        ('source/proof-peer-optimized.json','source/proof-peer-optimized.json'),
        ('source/RESIDUE_AND_DETERMINANT.md','source/RESIDUE_AND_DETERMINANT.md'),
        ('source/parent/PROOF.md','source/parent/PROOF.md'),('source/parent/LICENSE','source/parent/LICENSE'),
        ('source/independent_norm_oracle.py','source/independent_norm_oracle.py'),
        ('coefficients/BINDING.json','coefficients/BINDING.json'),
    ):files[target]=(PARENT/source).read_bytes()
    binding=json.loads(files['coefficients/BINDING.json'])
    for record in binding['payloads'].values():
        rel='coefficients/'+record['file'];files[rel]=(PARENT/rel).read_bytes()
    files['NODE_REMAP.json']=encoded(dict(schema='complete_two_cut_prefix_remap_v1',
        parent_sha256=PARENT_SHA,all_parent_nodes=records,inserted_child_nodes=inserted,
        first_norm_cut=dict(ell_parent=ell,k_parent=k,deleted_parent=[ellp,ellprod,k2],
            old_product_parent=product,new_product_child=mapping[product],
            new_L_child=inserted[0],new_Lplusk_child=inserted[1],
            identity='ell*(ell+1)*(k*k)=(ell*k)*((ell*k)+k)'),
        radix_square_cut=dict(q_parent=q,existing_q2_parent=q2,constant_two_parent=two,
            deleted_parent=twice_q,M_parent=M,new_M_child=mapping[M],
            identity='q*(2*q)=2*(q*q)'),
        semantics='Complete pointwise identity for every commutative ring. Removed private intermediates may be reconstructed from their recorded old definitions; they are not falsely claimed to equal some single retained node.'))
    files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,
        generator_sha256=digest(Path(__file__).read_bytes()),
        oracle_sha256=digest(files['source/independent_norm_oracle.py']),
        ordinary_proof_sha256=digest(files['source/ordinary-proof.md']),
        semantic_relation='Exact universal full-polynomial identity with121parent; same14unrestrictedintegerunknowns, allsixfixedports and degree312.',
        boundary='The frozen signed all-index proof and calibration are inherited unchanged. No new Lean, internal-ZFC derivation or PDF/TeX change.'))
    files['BUILD.json']=encoded(dict(status='PASS',integer_variables=14,operations=119,
        operation_counts=counts,exact_degree=312,norm_degree=256,
        sha256={name:digest(value)for name,value in files.items()}))
    return files


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for name,raw in build().items():
        path=OUT/name
        if args.check:need(path.read_bytes()==raw,'byte-identical '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,integer_variables=14,
                          operations=119,exact_degree=312),indent=2))


if __name__=='__main__':main()
