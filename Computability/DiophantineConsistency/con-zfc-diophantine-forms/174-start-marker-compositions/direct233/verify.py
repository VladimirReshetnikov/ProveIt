#!/usr/bin/env python3
"""Exact independent replay of the direct233 coefficient package (standard library).

The semantic proof is in PROOF.md. This checker establishes literal source
bindings, commutation with the retained chart, all new coordinate maps and all
expanded coefficients. It does not establish the inherited ZFC calibration.
"""
from pathlib import Path
import copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import audit_projection as A
import audit_parent_stage as B

def need(b,message):
    if not b:raise ValueError(message)
def read(p):return json.loads(p.read_text())
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def poly(row,n):return A.polynomial(row['terms'],n)
def replace_all(p,replacements):
    out={}
    for mon,c in p.items():
        term={():c}
        for i in mon:term=A.product(term,replacements.get(i,{(i,):1}))
        out=A.linear_combine(out,1,term)
    return out

def interface(source,edited):
    original=read(ROOT/'source/power245.json')
    names=original['variables'];n=len(names)
    need(n==245 and original['domain']=='unrestricted integers','245 source domain/count')
    names_to_indices={v['name']:i for i,v in enumerate(names)}
    f=names_to_indices['crt.growth_majorant_F'];r=names_to_indices['mul.1']
    q=names_to_indices['pow2.output'];z=names_to_indices['radix.odd_square_root_half']
    need((f,r,q,z)==(3,4,106,242),'245 interface coordinates')
    rows=[poly(row,n) for row in original['residuals']]
    need(rows[0]=={(f,f):-1,(r,):1},'245 radius row')
    qi=[i for i,p in enumerate(rows) if p=={():-2,(q,):1,(z,):-4,(z,z):-4}]
    need(qi==[179],'245 stored radix')
    sphere=[i for i,x in enumerate(original['residuals']) if x['label']=='domain_guard.4']
    need(sphere==[178],'245 sphere identity')
    p=rows[178];squares=[m for m,c in p.items() if c==-4]
    need(p.get(())==-1 and len(squares)==11 and all(len(m)==2 and m[0]==m[1] for m in squares),'sphere source shape')
    p.pop(())
    for m in squares:p[m]=-2
    stages=read(ROOT/'source/power239_stages.json')
    need(stages['family']=='power','wrong inherited family')
    ns,rs=B.compaction(names,copy.deepcopy(rows))
    ns,rs,count=B.replay(ns,rs,stages['stages'])
    need(ns==source['variables'] and rs==[poly(x,239) for x in source['residuals']], 'unmodified 245-to239 replay')
    rows[0]={(f,):-1,(r,):1};rows[179]={():-2,(q,):1,(z,):-4}
    ns,rs=B.compaction(names,copy.deepcopy(rows))
    ns,rs,_=B.replay(ns,rs,stages['stages'])
    need(ns==edited['variables'] and rs==[poly(x,239) for x in edited['residuals']], 'edited 245-to239 replay did not commute')
    return {'status':'PASS','source_variables':245,'target_variables':239,'inherited_stage_operations':count,'claim':'The two semantic row edits commute exactly with the retained 245-to239 chart. The arithmetic calibration remains an inherited theorem.'}

def semantic_projection():
    source_path=ROOT/'source/power239.json';source=read(source_path)
    edited=read(ROOT/'stages/linear237/edited_source239.json')
    result=read(ROOT/'stages/linear237/equation.json')
    certificate=read(ROOT/'stages/linear237/composition_certificate.json')
    need(source['domain']==edited['domain']==result['domain']=='unrestricted integers','domain')
    need(len(source['variables'])==239 and len(source['residuals'])==175,'source census')
    need(certificate['source_raw_sha256']==hashlib.sha256(source_path.read_bytes()).hexdigest(),'source bytes')
    need(source['variables']==edited['variables'],'semantic edits changed coordinates')
    expected=copy.deepcopy(source)
    need(poly(source['residuals'][0],239)=={(3,3):-1,(4,):1},'original radius row')
    need(poly(source['residuals'][173],239)=={():-2,(101,):1,(236,):-4,(236,236):-4},'original stored-radix row')
    expected['residuals'][0]['terms']=A.serial({(3,):-1,(4,):1})
    expected['residuals'][173]['terms']=A.serial({():-2,(101,):1,(236,):-4})
    need(expected['residuals']==edited['residuals'],'semantic edit changed other rows')
    need(poly(source['residuals'][155],239)=={():-16,(0,):1,(212,212):-2},'even horizon interface')
    need(poly(source['residuals'][154],239)=={(5,):-1,**{(5,i):-1 for i in range(9,18)},(211,):1},'representative-sum interface')
    mapping={4:{(3,):1},101:{():2,(236,):4}}
    keep=[i for i in range(239) if i not in mapping];ren={i:j for j,i in enumerate(keep)}
    need(certificate['removed_coordinates']==[4,101] and certificate['retained_coordinates']==keep,'coordinate maps')
    for k,v in certificate['affine_replacements'].items():need(A.polynomial(v,239,1)==mapping[int(k)],'recorded affine replacements')
    rows=[]
    for i,row in enumerate(edited['residuals']):
        p=replace_all(poly(row,239),mapping)
        if i in (0,173):need(not p,'deleted monic row survives');continue
        need(all(len(m)<=2 and not set(m)&set(mapping) for m in p),'substitution degree or liveness')
        rows.append({tuple(ren[j] for j in m):c for m,c in p.items()})
    need(result['variables']==[source['variables'][i] for i in keep],'target variable data')
    need(rows==[poly(row,237) for row in result['residuals']],'every projected residual')
    expanded=A.expanded_sos(result)
    need(A.polynomial(read(ROOT/'stages/linear237/expanded_polynomial.json')['terms'],237,4)==expanded,'237 expansion')
    need(read(ROOT/'stages/linear237/metrics.json')==A.metrics(result,expanded),'237 metrics')
    stage=interface(source,edited)
    return {'status':'PASS','semantic_rows':[0,173],'affine_restorations':{'R':'F','stored_q':'4z+2'},'metrics':A.metrics(result,expanded),'inherited_chart_interface':stage}

def main():
    provenance=read(ROOT/'PROVENANCE.json')
    for rel,d in provenance['local_sources'].items():
        b=(ROOT/rel).read_bytes()
        need(hashlib.sha256(b).hexdigest()==d['sha256'],'source sha256 '+rel)
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==d['git_blob_sha'],'source git blob '+rel)
    results={'source_and_semantic_projection':semantic_projection(),
      'radical_projection':A.audit(ROOT/'stages/linear237/equation.json',ROOT/'stages/radical234'),
      'affine_projection':A.audit_affine(ROOT/'stages/radical234/equation.json',ROOT/'stages/affine233'),
      'P233_balanced':A.audit_rows(ROOT/'stages/affine233/equation.json',ROOT/'equations/P233_balanced'),
      'P233_sparse':A.audit_rows(ROOT/'stages/affine233/equation.json',ROOT/'equations/P233_sparse'),
      'P234_sparse':A.audit_rows(ROOT/'stages/radical234/equation.json',ROOT/'equations/P234_sparse')}
    receipt={'status':'PASS','python_optimized':not __debug__,'results':results,
      'scope':'Exact new coefficient data, all projections and inverse maps, complete SOS expansions, source hashes and final inherited chart interface. Unbounded arithmetic proof is separate; no inherited logical calibration checker was replayed.'}
    if len(sys.argv)>1:Path(sys.argv[1]).write_bytes(canonical(receipt))
    print(json.dumps({'status':receipt['status'],'python_optimized':receipt['python_optimized'],
      'endpoints':{k:v['output_metrics'] for k,v in results.items() if k.startswith('P')},
      'source_interface':results['source_and_semantic_projection']['inherited_chart_interface'],
      'scope':receipt['scope']},indent=2))

if __name__=='__main__':main()
