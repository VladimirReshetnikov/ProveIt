#!/usr/bin/env python3
"""Build a signed three-root/quadratic-projection121-operation endpoint."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
PARENT=ROOT/'candidates/constructive-integer14-shared'
OUT=ROOT/'candidates/constructive-integer14-quadratic'
PARENT_SHA='0e9f89dfdcc8a27feed8a278d46b04b10c88d24cec76a190444eb9b7e2b0fa7b'
ARCHIVE=REPO/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
ARCHIVE_SHA='37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0'
BORROWED='ConZFC_Constructive_Reductions_2026-10-23/integer14/upstream/provenance/RESIDUE_AND_DETERMINANT.md'


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()


def encoded(value):return(json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def build():
    raw=(PARENT/'equation.json').read_bytes()
    need(digest(raw)==PARENT_SHA,'frozen145integerparent')
    parent=json.loads(raw);old=parent['nodes'];named=parent['named_registers']
    need(digest(ARCHIVE.read_bytes())==ARCHIVE_SHA,'originalwholearchive')
    with zipfile.ZipFile(ARCHIVE)as z:borrowed=z.read(BORROWED)
    need(old[named['Dmain']]==['add',22,named['Dmain']-1]and
         old[named['Dm']]==['mul',named['Dmain'],named['Dm']-1], 'literalmainrootcut')
    deleted={named['Dmain']-1,named['Dmain'],named['Dm']-1,named['Dm']}
    constants={r[1]:i for i,r in enumerate(old)if r[0]=='integer'}
    nodes=[];mapping={};retained=[];new_projection=[]
    def gate(op,a,b):
        i=len(nodes);nodes.append([op,a,b]);return i
    for i,row in enumerate(old[:named['Cn']+1]):
        if i in deleted:continue
        if i==named['b0']:
            x,ac=mapping[row[1]],mapping[row[2]]
            ac2=gate('mul',mapping[constants[2]],ac)
            xa=gate('add',x,ac2)
            prod=gate('mul',x,xa)
            mapping[i]=gate('sub',prod,mapping[constants[1]])
            new_projection=list(range(ac2,mapping[i]+1))
        else:
            mapping[i]=len(nodes)
            nodes.append([row[0],mapping[row[1]],mapping[row[2]]]
                         if row[0]in('add','sub','mul')else deepcopy(row))
            retained.append(dict(parent=i,child=mapping[i]))
    prefix_length=len(nodes)
    new_named={k:mapping[i]for k,i in named.items()if i in mapping and k not in('b0','A','B','N','output')}
    new_named['K']=mapping[named['b0']]
    new_named['raw_A']=mapping[named['A']]
    new_named['raw_B']=mapping[named['B']]
    tail_start=len(nodes)
    z2=gate('mul',mapping[named['center']],mapping[named['center']])
    fs=gate('mul',mapping[named['delta']],z2)
    fa=gate('mul',mapping[named['delta']],mapping[named['A']])
    fb=gate('mul',mapping[named['delta']],mapping[named['B']])
    fc=mapping[named['Cn']]
    up=gate('add',fs,fc);ab=gate('add',fa,fb);po=gate('sub',up,ab)
    sc=gate('mul',fs,fc);axb=gate('mul',fa,fb);sm=gate('add',sc,axb)
    f4=gate('mul',mapping[constants[4]],sm);po2=gate('mul',po,po)
    pe=gate('sub',po2,f4);pe2=gate('mul',pe,pe);pair=gate('mul',sc,axb)
    c64=len(nodes);nodes.append(['integer',64])
    scaled=gate('mul',c64,pair);N=gate('sub',pe2,scaled)
    new_named.update(dict(fs=fs,fa=fa,fb=fb,fc=fc,N=N))
    tail_end=len(nodes)
    mapping[named['N']]=N
    finalizer_map=[]
    for i in range(named['N']+1,len(old)):
        row=old[i];mapping[i]=gate(row[0],mapping[row[1]],mapping[row[2]])
        finalizer_map.append(dict(parent=i,child=mapping[i]))
    new_named['output']=mapping[parent['output']]
    child=deepcopy(parent)
    child.update(name='crt14_quadratic_projection_degree312',nodes=nodes,output=mapping[parent['output']],
        named_registers=new_named,parent_sha256=PARENT_SHA,proof='PROOF.md',exact_degree=312,
        norm_exact_degree=256,
        proof_status='New signed ordinary zero-existence equivalence with145parent via abs-folding, cubic CRT before signed bootstrap, whole-product quadratic projection and unrestricted n maps. Not a full-polynomial identity; no new native calibration or Lean/internal-ZFC proof.')
    counts=dict(Counter(r[0]for r in nodes if r[0]in('add','sub','mul')))
    child['operation_counts']=counts;child['operations']=sum(counts.values())
    need(child['operations']==121 and counts=={'mul':70,'add':26,'sub':25},'actualcomplete121operations')
    files={'equation.json':encoded(child),'source/parent-equation.json':raw,
        'source/RESIDUE_AND_DETERMINANT.md':borrowed}
    for target,source in(
        ('source/parent-proof.md','README.md'),
        ('source/parent/PROOF.md','source/parent/PROOF.md'),
        ('source/parent/LICENSE','source/parent/LICENSE'),
        ('source/parent-check.json','CHECK.json'),
        ('source/parent-check-optimized.json','CHECK_OPTIMIZED.json'),
        ('source/ordinary-peer.md','source/ordinary-peer.md'),
        ('source/original-review.json','source/original-review.json'),
        ('source/original-review-optimized.json','source/original-review-optimized.json'),
        ('source/independent_norm_oracle.py','source/independent_norm_oracle.py'),
        ('coefficients/BINDING.json','coefficients/BINDING.json'),
    ):files[target]=(PARENT/source).read_bytes()
    for target,source in(
        ('source/proof-peer.md','signed14-quadratic-peer.md'),
        ('source/proof-peer.py','signed14-quadratic-peer.py'),
        ('source/proof-peer.json','signed14-quadratic-peer.json'),
        ('source/proof-peer-optimized.json','signed14-quadratic-peer_OPTIMIZED.json'),
    ):files[target]=(ROOT/'reviews'/source).read_bytes()
    binding=json.loads(files['coefficients/BINDING.json'])
    for record in binding['payloads'].values():
        rel='coefficients/'+record['file'];files[rel]=(PARENT/rel).read_bytes()
    files['PREFIX_REMAP.json']=encoded(dict(schema='complete_signed_projection_norm_replacement_v1',
        parent_sha256=PARENT_SHA,parent_prefix_last=named['Cn'],child_prefix_length=prefix_length,
        retained_prefix=retained,deleted_prefix=[dict(parent=i,row=old[i])for i in sorted(deleted)],
        replaced_projection=dict(parent=named['b0'],old_row=old[named['b0']],
            child_indices=new_projection,new_rows=[nodes[i]for i in new_projection],new_K=mapping[named['b0']]),
        old_norm_indices=list(range(named['Cn']+1,named['N']+1)),
        new_norm_indices=list(range(tail_start,tail_end)),
        finalizer=finalizer_map,
        semantic_scope='Retained definitions copied with all remapped operands. Center values change; zero-existence equivalence is the signed PROOF.md, not a complete output ring identity.'))
    files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,
        archive_sha256=ARCHIVE_SHA,borrowed_member=BORROWED,borrowed_prefix_sha256=digest(borrowed),
        borrowed_scope='Section4 up to the sign-uniform ratio, before its main-projection/orientation step. Newproof verifies every premise before invoking it.',
        generator_sha256=digest(Path(__file__).read_bytes()),
        oracle_sha256=digest(files['source/independent_norm_oracle.py']),
        semantic_relation='Equivalence of existence of unrestricted integer zeros, with explicit unrestricted n maps. Signed variables never assumed positive.',
        boundary='Same original sixcoefficients and source34 ordinarycalibration; oldzero restored before compiler theorem. Lean remains paused.'))
    files['BUILD.json']=encoded(dict(status='PASS',integer_variables=14,operations=121,
        operation_counts=counts,exact_degree=312,norm_degree=256,
        sha256={name:digest(blob)for name,blob in files.items()}))
    return files


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for name,raw in build().items():
        path=OUT/name
        if args.check:need(path.read_bytes()==raw,'byte-identical '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,integer_variables=14,
                          operations=121,exact_degree=312),indent=2))


if __name__=='__main__':main()
