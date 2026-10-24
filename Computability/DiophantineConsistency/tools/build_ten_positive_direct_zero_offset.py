#!/usr/bin/env python3
"""Materialize the combined ten-positive105-operation, degree340 equation."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
DIRECT=ROOT/'candidates/ten-positive-direct-base'
ZERO=ROOT/'candidates/ten-positive-zero-offset'
OUT=ROOT/'candidates/ten-positive-direct-zero-offset'
DIRECT_SHA='63367b3b3a8f7ca35af73677ecd1c518578e59a3627a1e9d7a43550a7d391f49'
ZERO_SHA='047ea8145ef52ab939322f2147c75272e7a182016be78a453fbdf2d3c2a6a493'


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(data):return sha256(data).hexdigest()
def encoded(obj):return(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()


def build():
    direct_raw=(DIRECT/'equation.json').read_bytes();zero_raw=(ZERO/'equation.json').read_bytes()
    need(digest(direct_raw)==DIRECT_SHA and digest(zero_raw)==ZERO_SHA,'both complete accepted parent equations')
    parent=json.loads(direct_raw);zero=json.loads(zero_raw);old=parent['source']
    need(parent['coefficient_binding']==zero['coefficient_binding'],'same whole coherent four-port family')
    need(old[5:7]==[['E','*','X','Y'],['a','+','E','Y']]and old[12:14]==[['a2','+','a',2],['Am1','*','mu','a2']]
         and old[18]==['muY','*','mu','Y'],'actual private base and existing shared product')
    need([i for i,r in enumerate(old)if'E'in r[2:]]==[6]and[i for i,r in enumerate(old)if'a'in r[2:]]==[12]
         and[i for i,r in enumerate(old)if'a2'in r[2:]]==[13],'entire private consumer boundary')
    schedule=list(range(5))+list(range(7,12))+['insert_Xp1',18]+list(range(13,18))+list(range(19,107))
    rows=[];positions={}
    for i in schedule:
        if i=='insert_Xp1':rows.append(['Xp1','+','X',1]);continue
        positions[i]=len(rows);rows.append(['Am1','*','muY','Xp1']if i==13 else deepcopy(old[i]))
    records=[]
    for i,row in enumerate(old):
        if i in[5,6,12]:records.append(dict(parent_index=i,status='deleted_private',old_row=row));continue
        j=positions[i];records.append(dict(parent_index=i,child_index=j,old_row=row,new_row=rows[j],
            status='replaced_base_operand'if i==13 else'moved_shared'if i==18 else'retained'))
    counts=dict(Counter(r[1]for r in rows));need(len(rows)==105 and counts=={'*':63,'+':24,'-':18},'actual105-operation inventory')
    degrees={v:1 for v in parent['witnesses']}|{v:0 for v in parent['fixed_numerals']}
    for n,o,a,b in rows:
        da,db=(0 if type(v)is int else degrees[v]for v in(a,b));degrees[n]=da+db if o=='*'else max(da,db)
    child=deepcopy(parent);child.update(name='ten_positive_direct_zero_offset_degree340',source=rows,operations=105,
        operation_breakdown=counts,exact_degree=340,syntactic_degree=degrees['N'],
        register_degrees={k:degrees[k]for k in parent['register_degrees']if k!='a'},
        parent_sha256=DIRECT_SHA,zero_offset_parent_sha256=ZERO_SHA,proof='PROOF.md',
        proof_status='Ordinary positive-zero/refutation equivalence: zero-offset ratio at X>=q, direct carrier with delayed q|X, completeness from accepted99zerooffset. No newLean/internal-ZFC endpoint.')
    files={'equation.json':encoded(child),'PROOF.md':(OUT/'PROOF.md').read_bytes()};deps={}
    for label,path,pin in [('direct',DIRECT,DIRECT_SHA),('zero',ZERO,ZERO_SHA)]:
        for name in ['equation.json','PROOF.md','CHECK.json','CHECK_OPTIMIZED.json','MANIFEST.json']:
            n='source/'+label+'/'+name;files[n]=(path/name).read_bytes();deps[n]=path/name
        for p in(path/'source').rglob('*'):
            if p.is_file():
                n='source/'+label+'/'+str(p.relative_to(path));files[n]=p.read_bytes();deps[n]=p
    for suffix in ['md','json']:
        p=ROOT/('reviews/ten-positive-direct-zero-offset-ordinary-peer.'+suffix)
        n='source/COMBINED_ORDINARY_PEER.'+suffix;files[n]=p.read_bytes();deps[n]=p
    oracle=DIRECT/'source/independent_norm_oracle.py';files['source/independent_norm_oracle.py']=oracle.read_bytes();deps['source/independent_norm_oracle.py']=oracle
    files['coefficients/BINDING.json']=(DIRECT/'coefficients/BINDING.json').read_bytes()
    for pin in parent['coefficient_binding']['ports'].values():
        n='coefficients/'+pin['file'];data=(DIRECT/n).read_bytes();need(data==(ZERO/n).read_bytes(),'whole parent coefficient bytes '+n);files[n]=data
    files['CUTS.json']=encoded(dict(direct_parent_sha256=DIRECT_SHA,zero_offset_parent_sha256=ZERO_SHA,
        all_parent_rows=records,deleted_parent_indices=[5,6,12],changed_parent_indices=[13],moved_parent_indices=[18],
        inserted_child_rows=[dict(child_index=10,new_row=['Xp1','+','X',1])],parent_norm_tail_start=94,child_norm_tail_start=92,
        shared_base_identity='mu*(X*Y+Y)=(mu*Y)*(X+1)',
        complete_zero_parent_map='Keep X and all kernels; x=X-q; n_new=n99+(W_new-W99)*t+u, (q-1)t=Bt, q^4*u=X.',
        universal_center_cut='Z_new-q*Z99=H*mu^2*[q^4*DeltaW*((q-1)*t-Bt)+(q-1)*(q^4*u-X)]',
        output_map='B_new=q*Bt99, M_new=q*M99, Z_new=q*Z99, output_new=q^8*output99 once both stated integer residuals vanish.',
        boundary='No pointwise equality with direct107, whose A differs. Ordinary soundness does not use q|X before whole-product projection.'))
    changes={4:['X','+','q','x'],34:['qK0X','+','qK0','X'],35:['qK0XC','*','qK0X','C'],36:['B','-','qK0XC','qF'],
        54:['qm1L','*','qbJ','L'],56:['P1','*','q4','bJ'],68:['lowY','*','qbJ','Y'],69:['WBt','*','W','B'],71:['inner0','-','lowY','q3WBt']}
    before={34:[['qK0','*','q','K0']],36:[['qF','*','q','F']],54:[['qbJ','*','q','bJ']],56:[['q4','*','q3','q']],71:[['lowX','*','bJ','X']]}
    after={71:[['inner','-','inner0','lowX']]};zero_rows=[];zero_records=[];insertions=[]
    for j,old_row in enumerate(zero['source']):
        for row in before.get(j,[]):insertions.append(dict(parent_index=j,position='before',child_index=len(zero_rows),row=row));zero_rows.append(row)
        new=deepcopy(changes.get(j,old_row));zero_records.append(dict(parent_index=j,child_index=len(zero_rows),old_row=old_row,new_row=new,
            status='replaced_carrier_cut'if j in changes else'retained'));zero_rows.append(new)
        for row in after.get(j,[]):insertions.append(dict(parent_index=j,position='after',child_index=len(zero_rows),row=row));zero_rows.append(row)
    need(zero_rows==rows,'entire independent99-to105 construction commutes with107-to105 construction')
    files['ZERO_PARENT_CUTS.json']=encoded(dict(zero_parent_sha256=ZERO_SHA,all_parent_rows=zero_records,inserted_rows=insertions,
        changed_parent_indices=sorted(changes),parent_norm_tail_start=86,child_norm_tail_start=92,
        boundary='All unchanged kernel rows retain literal operands; X=q*w is replaced by X=q+x with licensed x=X_old-q. Six inserted primitive carrier definitions are completely listed.'))
    files['PROVENANCE.json']=encoded(dict(direct_parent_equation_sha256=DIRECT_SHA,zero_parent_equation_sha256=ZERO_SHA,
        generator_sha256=digest(Path(__file__).read_bytes()),
        dependencies={n:dict(repository_path=str(p.relative_to(ROOT)),sha256=digest(files[n]))for n,p in deps.items()},
        coefficient_family='Entire coherent originalcompact44 tuple unchanged. The separate coherentBFS44 specialization uses inherited uniform native/controller source proof; no port mixing.',
        canonical_page_unchanged=True,boundary='Ordinary unbounded proof with explicit positive completeness map from99; no newLean/internal-ZFC theorem.'))
    files['SOURCE_PINS.json']=encoded(dict(schema='ten_positive_direct_zero_offset_source_pins_v1',
        direct_parent_equation_sha256=DIRECT_SHA,direct_parent_manifest_sha256=digest((DIRECT/'MANIFEST.json').read_bytes()),
        zero_parent_equation_sha256=ZERO_SHA,zero_parent_manifest_sha256=digest((ZERO/'MANIFEST.json').read_bytes()),
        ordinary_proof_sha256=digest(files['PROOF.md']),generator_repository_path=str(Path(__file__).relative_to(ROOT)),generator_sha256=digest(Path(__file__).read_bytes())))
    files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=105,operation_breakdown=counts,
        exact_degree=340,syntactic_degree=degrees['N'],sha256={n:digest(data)for n,data in files.items()}))
    return files


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for n,data in build().items():
        p=OUT/n
        if args.check:need(p.read_bytes()==data,'byte-identical complete artifact '+n)
        else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,positive_variables=10,operations=105,exact_degree=340),indent=2))


if __name__=='__main__':main()
