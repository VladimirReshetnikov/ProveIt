#!/usr/bin/env python3
"""Independent bindings, exact coefficient replay, optional isolated rebuild.

New transformation checks import no construction module. Retained source and
projection checkers are separate implementations from their producers.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
def require(c,s):
    if not c:raise ValueError(s)
def read(p):return json.loads(p.read_text())
def module(name,p):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def collect(terms):
    out={}
    for c,m in terms:
        require(type(c)is int and all(type(v)is int for v in m),'nonintegral coefficient/index')
        key=tuple(sorted(m));out[key]=out.get(key,0)+c
    return {m:c for m,c in out.items() if c}
def dump(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):return collect([(c,m) for p in ps for m,c in p.items()])
def scale(p,c):return {m:v*c for m,v in p.items() if c*v}
def multiply(p,q):return collect([(a*b,m+n) for m,a in p.items() for n,b in q.items()])
def substitute(p,v,q):
    terms=[]
    for mon,c in p.items():
        term={():c}
        for u in mon:term=multiply(term,q if u==v else {(u,):1})
        terms.extend((c,m) for m,c in term.items())
    return collect(terms)

def verify_transform(parent,meta,affine_certificate,source):
    old_to_raw={v:i for i,v in enumerate(affine_certificate['retained_original_indices_in_target_order'])}
    def atom(expr):
        p={():expr[1]} if expr[0]=='c' else {(expr[1],):1}
        for step in affine_certificate['steps']:
            v=step['variable_original_index']
            if any(v in m for m in p):p=substitute(p,v,collect(step['restoration']))
        require(all(v in old_to_raw for m in p for v in m),'semantic atom not expressible in raw source')
        return {tuple(old_to_raw[v] for v in m):c for m,c in p.items()}
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    require(len(names)==len(parent['variables']),'duplicate original names')
    C1={():1}
    A=atom(meta['cap']['base']);H=atom(meta['cap']['index']);V=atom(meta['cap']['pair'][1])
    error={}
    for seed in meta['cap_residue']['seeds']:
        diff=add(atom(seed['pair'][1]),scale(atom(seed['exponent']),-1))
        error=add(error,multiply(diff,diff))
    qold=names['index_cap.error_square_quotient']
    fused=add(H,error,multiply(add(A,scale(C1,-1)),{(qold,):1}),scale(V,-1))
    groups=[['choose0','crt.range.index'],['crt.range.a','crt.range.b','crt.range.c','crt.range.d','crt.range.derived_label_sum'],['crt.range.S','crt.range.Sp'],['crt.range.u','crt.range.vq']]
    tags=['t0','t','y','x'];request={r['label']:r for r in meta['modular_requests']}
    pooled={};removed_labels=set();renamed=deepcopy(parent['variables'])
    for tag,g in zip(tags,groups):
        den=atom(request[g[0]]['den'])
        require(all(atom(request[s]['den'])==den for s in g),'unequal denominators pooled')
        slack=atom(request[g[0]]['remainder_slack'])
        p=add(den,scale(C1,-1),scale(slack,-1),*[scale(atom(request[s]['remainder']),-1) for s in g])
        pooled[g[0]+'.remainder_bound']={'label':'pooled_digits.'+tag,'terms':dump(p)}
        removed_labels.update(s+'.remainder_bound' for s in g[1:])
        for mon,c in slack.items():
            require(len(mon)==1 and c==1,'expected a free slack coordinate')
            renamed[mon[0]]['name']='pooled_digits.'+tag+'.slack'
    aggregate_names=['index_cap.aggregate_slack','add.589','add.593','add.597','add.601']
    dead={names[n] for n in aggregate_names}
    deadrows=[r for r in parent['residuals'] if any(v in dead for _,m in r['terms'] for v in m)]
    require(len(deadrows)==5,'wrong old cap-sum closure')
    # Prove exactly which old aggregate inequality that private chain represents.
    old_bound=next(r for r in parent['residuals'] if r['label']=='index_cap.all_indices_bound')
    expanded=collect(old_bound['terms'])
    for variable in reversed(aggregate_names[1:]):
        v=names[variable]
        defining=[r for r in deadrows if collect(r['terms']).get((v,))==1]
        require(len(defining)==1,'ambiguous aggregate gate definition')
        p=collect(defining[0]['terms']);del p[(v,)]
        expanded=substitute(expanded,v,scale(p,-1))
    expected=add(V,scale(H,-1),scale(C1,-1),{(names[aggregate_names[0]],):-1},*[scale(atom(s['pair'][1]),-1) for s in meta['cap_residue']['seeds']])
    require(expanded==expected,'old aggregate cap has unexpected meaning')
    rows=[]
    renamed[qold]['name']='index_cap.fused_quotient'
    for r in parent['residuals']:
        if r in deadrows or r['label'] in removed_labels:continue
        if r['label'] in pooled:rows.append(pooled[r['label']])
        elif r['label']=='index_cap.squared_index_errors':rows.append({'label':'index_cap.fused_bound_errors','terms':dump(fused)})
        else:rows.append(deepcopy(r))
    live=sorted({v for r in rows for _,m in r['terms'] for v in m});rename={v:i for i,v in enumerate(live)}
    for r in rows:r['terms']=[[c,[rename[v] for v in m]] for c,m in r['terms']]
    require(source['variables']==[renamed[v] for v in live],'new variable/domain map differs')
    require(source['residuals']==rows,'literal source transformation differs')
    require(source['domain']=='nonnegative integers','wrong new source domain')
    require(len(live)==332 and len(rows)==281,'wrong new raw dimensions')
    require(max(len(m) for r in rows for _,m in r['terms'])==2,'nonquadratic new source')
    return {'verified':True,'group_sizes':list(map(len,groups)),'seed_squares':len(meta['cap_residue']['seeds']),'retained_literal_rows':len(rows),'variables':len(live),'all_source_rows_compared':True,'H_in_parent_raw_coordinates':dump(H)}

def coefficient_check(equation,expanded):
    total={}
    for r in equation['residuals']:
        p=collect(r['terms']);total=add(total,multiply(p,p))
    require(dump(total)==expanded['terms'],'expanded polynomial mismatch')
    require(expanded['domain']==equation['domain'],'coefficient domain mismatch')
    require(expanded['variables']==len(equation['variables']),'coefficient variable count mismatch')
    actual={'variables':len(equation['variables']),'quadratic_rows':len(equation['residuals']),'exact_degree':max(map(len,total)),'expanded_monomials':len(total),'max_abs_expanded_coefficient':max(map(abs,total.values())),'max_abs_row_coefficient':max(abs(c) for r in equation['residuals'] for c,m in r['terms'])}
    require(all(equation['metrics'][k]==v for k,v in actual.items()),'metric mismatch')
    require({v for m in total for v in m}==set(range(actual['variables'])),'unused final variable')
    return actual

def verify(rebuild=False):
    pins=read(ROOT/'UPSTREAM_PINS.json')
    for f in pins['files']:
        b=(ROOT/f['path']).read_bytes()
        require(len(b)==f['bytes'],'pinned byte size changed')
        require(hashlib.sha256(b).hexdigest()==f['sha256'],'pinned SHA256 changed')
        require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==f['git_blob_sha1'],'pinned Git blob changed')
    parent=read(ROOT/'upstream/129-semantic-pell-anchor/equations/source/equation.json')
    meta=read(ROOT/'upstream/129-semantic-pell-anchor/equations/source/semantic.json')
    affine=module('retained_affine_checker',ROOT/'upstream/129-semantic-pell-anchor/code/check_affine_export.py')
    semantic=module('retained_semantic_checker',ROOT/'upstream/129-semantic-pell-anchor/code/check_semantics.py')
    afreceipt,afcertificate=affine.verify(meta,parent)
    semreceipt=semantic.Audit(meta).run()
    source=read(ROOT/'equations/source/equation.json')
    transform=verify_transform(parent,meta,afcertificate,source)
    smet=coefficient_check(source,read(ROOT/'equations/source/expanded_polynomial.json'))
    projector=module('independent_projection_checker',ROOT/'upstream/100-quartics407-888/code/psd_contract/check.py')
    endpoints={}
    for n in [226,227]:
        p=ROOT/'equations'/('natural'+str(n));eq=read(p/'equation.json');cert=read(p/'elimination_certificate.json');expanded=read(p/'expanded_polynomial.json')
        receipt,terms=projector.verify(source,eq,cert)
        require(terms==expanded['terms'],'independent projection coefficient mismatch')
        endpoints[str(n)]={'metrics':coefficient_check(eq,expanded),'projection':receipt}
    integer=read(ROOT/'equations/integer678.json')
    require(integer['domain']=='unrestricted integers' and integer['variables']==678 and integer['exact_degree']==8,'integer recipe metrics')
    expected=[[[1,[3*i,3*i]],[1,[3*i+1,3*i+1]],[1,[3*i+2,3*i+2]],[1,[3*i+2]]] for i in range(226)]
    require(integer['substitutions']==expected,'integer substitution differs')
    controls=[]
    for label in ['pooled_digits.t','index_cap.fused_bound_errors']:
        bad=deepcopy(source);r=next(r for r in bad['residuals'] if r['label']==label);r['terms'][0][0]+=1
        try:verify_transform(parent,meta,afcertificate,bad)
        except ValueError:controls.append(label+' coefficient alteration rejected')
        else:raise ValueError('corruption was accepted')
    result={'verified':True,'optimized':not __debug__,'upstream_git_blobs_checked':len(pins['files']),'inherited_affine':afreceipt,'inherited_local_semantics':semreceipt,'new_source_transformation':transform,'new_source_metrics':smet,'endpoints':endpoints,'integer_companion':'678 integer variables; literal g substitutions checked','negative_controls':controls,'scope':'exact finite source, substitution and coefficient checks; unbounded arithmetic proof is PROOF.md; inherited logical calibration not reproved'}
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='pooled-digits-rebuild-')as tmp:
            dest=Path(tmp);command=[sys.executable]+(['-O'] if not __debug__ else [])+['-B',str(ROOT/'code/build.py'),'--output',str(dest)]
            p=subprocess.run(command,capture_output=True,text=True)
            require(p.returncode==0,'rebuild failed: '+p.stderr)
            generated=sorted(p for p in dest.rglob('*') if p.is_file())
            for p in generated:require(p.read_bytes()==(ROOT/p.relative_to(dest)).read_bytes(),'rebuild bytes differ: '+str(p.relative_to(dest)))
            result['rebuild_byte_identical_files']=[str(p.relative_to(dest)) for p in generated]
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--rebuild',action='store_true');ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    result=verify(a.rebuild);text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if a.receipt:a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(text)
    print(text)
