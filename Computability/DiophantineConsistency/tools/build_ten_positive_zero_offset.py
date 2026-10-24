#!/usr/bin/env python3
"""Materialize the99-operation ten-positive zero-offset sibling, degree368."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-short-projection'
OUT=ROOT/'candidates/ten-positive-zero-offset'
PROOF=ROOT/'research/ten-positive-zero-offset/PROOF.md'
PARENT_SHA='cf2748fc277a20a419f196d28674e5374316d5f29fae5ef49c7b113e13b19edd'


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(x):return sha256(x).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()


def build():
    raw=(PARENT/'equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'whole frozen101 parent')
    parent=json.loads(raw);old=parent['source']
    need(old[12:14]==[['a2','+','a',2],['Am1','*','mu','a2']],'actual private offset and base product')
    need([i for i,r in enumerate(old)if'a2'in r[2:]]==[13],'offset gate has exactly one consumer')
    need(old[5:7]==[['E','*','X','Y'],['a','+','E','Y']]and old[18]==['muY','*','mu','Y'],'existing product/addition and sharedmuY cuts')
    need([i for i,r in enumerate(old)if'E'in r[2:]]==[6]and[i for i,r in enumerate(old)if'a'in r[2:]]==[12],
         'E and a have only their listed private consumers')
    schedule=list(range(5))+list(range(7,12))+['insert_Xp1',18]+list(range(13,18))+list(range(19,101))
    rows=[];positions={}
    for i in schedule:
        if i=='insert_Xp1':rows.append(['Xp1','+','X',1]);continue
        positions[i]=len(rows);rows.append(['Am1','*','muY','Xp1']if i==13 else deepcopy(old[i]))
    records=[]
    for i,row in enumerate(old):
        if i in[5,6,12]:records.append(dict(parent_index=i,status='deleted_private',old_row=row));continue
        j=positions[i];records.append(dict(parent_index=i,child_index=j,old_row=row,new_row=rows[j],
            status='replaced_base_operand'if i==13 else'moved_shared'if i==18 else'retained'))
    child=deepcopy(parent);counts=dict(Counter(r[1]for r in rows))
    need(len(rows)==99 and counts=={'*':59,'+':23,'-':17},'actual99 operation inventory')
    degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
    for n,o,a,b in rows:
        da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db)
    child.update(name='ten_positive_zero_offset_degree368',source=rows,operations=99,operation_breakdown=counts,
        exact_degree=368,syntactic_degree=degrees['N'],register_degrees={k:degrees[k]for k in parent['register_degrees']if k!='a'},
        parent_sha256=PARENT_SHA,proof='PROOF.md',
        proof_status='Ordinary fresh canonical zero/refutation equivalence at A=mu*a+1 using new ratio bounds. No pointwise old/new witness map, newLean or internal-ZFC theorem.')
    deps={'PROOF.md':PROOF,'source/short-parent-equation.json':PARENT/'equation.json',
        'source/SHORT_PROOF.md':PARENT/'PROOF.md','source/short-parent-check.json':PARENT/'CHECK.json',
        'source/short-parent-check-optimized.json':PARENT/'CHECK_OPTIMIZED.json',
        'source/SHORT_PARENT_MANIFEST.json':PARENT/'MANIFEST.json'}
    files={n:p.read_bytes()for n,p in deps.items()};files['equation.json']=encoded(child)
    for p in(PARENT/'source').rglob('*'):
        if p.is_file():n=str(p.relative_to(PARENT));files[n]=p.read_bytes();deps[n]=p
    for n,pin in json.loads((PARENT/'PROVENANCE.json').read_bytes())['dependencies'].items():deps[n]=ROOT/pin['repository_path']
    for suffix in['md','json','py','_OPTIMIZED.json']:
        separator=''if suffix.startswith('_')else'.'
        p=ROOT/('reviews/ten-positive-zero-offset-ordinary-peer'+separator+suffix)
        n='source/ZERO_OFFSET_ORDINARY_PEER'+separator+suffix;files[n]=p.read_bytes();deps[n]=p
    files['coefficients/BINDING.json']=(PARENT/'coefficients/BINDING.json').read_bytes()
    for pin in parent['coefficient_binding']['ports'].values():
        n='coefficients/'+pin['file'];files[n]=(PARENT/n).read_bytes()
    files['CUTS.json']=encoded(dict(parent_sha256=PARENT_SHA,all_parent_rows=records,
        deleted_parent_indices=[5,6,12],changed_parent_indices=[13],moved_parent_indices=[18],
        inserted_child_rows=[dict(child_index=10,new_row=['Xp1','+','X',1])],parent_norm_tail_start=88,child_norm_tail_start=86,
        base_parameter_change='A_full_new=A_full_parent-2*mu; A_page=Am1',
        unchanged_front_prefix_through=4,all_other_definitions_unchanged=True,
        shared_base_identity='mu*(X*Y+Y)=(mu*Y)*(X+1)',
        boundary='The changedbase propagates through all dependent kernels. Equivalence is by the newordinaryratio/source proof andfresh canonical witnesses, not pointwise parent/child input equality.'))
    files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,generator_sha256=digest(Path(__file__).read_bytes()),
        dependencies={n:dict(repository_path=str(p.relative_to(ROOT)),sha256=digest(files[n]))for n,p in deps.items()},
        coefficient_family='Entire coherent originalcompact44 tuple unchanged; entireBFS44 separatelylicensed by inherited uniform source/native/controller proof. No individual payload substitution.',
        canonical_page_unchanged=True,boundary='Ordinary unbounded fresh-witness proof; no newLean/internal-ZFC endpoint.'))
    files['SOURCE_PINS.json']=encoded(dict(schema='ten_positive_zero_offset_source_pins_v1',parent_equation_sha256=PARENT_SHA,
        parent_manifest_sha256=digest((PARENT/'MANIFEST.json').read_bytes()),ordinary_proof_sha256=digest(PROOF.read_bytes()),
        generator_repository_path=str(Path(__file__).relative_to(ROOT)),generator_sha256=digest(Path(__file__).read_bytes())))
    files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=99,operation_breakdown=counts,
        exact_degree=368,syntactic_degree=degrees['N'],sha256={n:digest(data)for n,data in files.items()}))
    return files


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    for n,data in build().items():
        p=OUT/n
        if args.check:need(p.read_bytes()==data,'byte-identical complete artifact '+n)
        else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,positive_variables=10,operations=99,exact_degree=368),indent=2))


if __name__=='__main__':main()
