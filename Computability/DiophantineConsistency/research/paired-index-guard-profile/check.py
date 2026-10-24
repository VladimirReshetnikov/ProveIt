#!/usr/bin/env python3
"""Optimizer-free full-row domain, Z-inverse and quartic profile checks."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos

def need(b,s):
    if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def digest(b):return sha256(b).hexdigest()
def module(n,p):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def poly(ts):
    p={}
    for c,m in ts:
        need(type(c)is int and all(type(v)is int and v>=0 for v in m),'integer coefficient/index')
        k=tuple(sorted(m));p[k]=p.get(k,0)+c
    return {m:c for m,c in p.items()if c}
def add(p,q):
    r=dict(p)
    for m,c in q.items():r[m]=r.get(m,0)+c
    return {m:c for m,c in r.items()if c}
def mul(p,q):
    r={}
    for m,c in p.items():
        for n,d in q.items():k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
    return {m:c for m,c in r.items()if c}
def sub(p,images):
    r={}
    for m,c in p.items():
        t={():c}
        for v in m:t=mul(t,images[v])
        r=add(r,t)
    return r
def reject(label,f):
    try:f()
    except(ValueError,RuntimeError,KeyError,IndexError,TypeError):return label
    raise ValueError('corruption accepted '+label)

def domain(eq,cert,family,mode,raw,body,restore,old,proof):
    retained=restore['retained_raw_indices']
    if family=='raw':variables=raw['variables'];rows=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']];mp={i:i for i in range(1259)}
    else:variables=body['variables'];rows=body['residuals'];mp={v:i for i,v in enumerate(retained)}
    n=len(variables);nr=len(rows);extra=int(mode=='wire')
    need(eq['domain']=='unrestricted integers' and eq['variables'][:n]==variables and eq['residuals'][:nr]==rows,'complete original body coefficients and metadata fixed')
    need(cert['baseline_body_variables']==n and cert['baseline_body_rows']==nr and cert['baseline_raw_indices']==list(mp),'complete baseline raw-coordinate binding')
    need(len(eq['variables'])==n+extra+231 and len(eq['residuals'])==nr+extra+77,'literal77-guard dimensions')
    keep=[g['raw_variable']for g in old['guards']if g['raw_variable']not in[674,861,1214]]
    need(len(keep)==75 and sorted(keep)==proof['retained_scalar_guards'],'exact75 retained scalar predicates')
    if extra:
        need(cert['product_wire']==n and eq['variables'][n]==dict(kind='gate',name='paired_index.product_wire'),'one explicit product wire')
        need(eq['residuals'][nr]==dict(label='paired_index.product_definition',terms=[[1,[n]],[-1,[mp[674],mp[861]]]]),'complete monic product definition')
    else:need(cert['product_wire']is None,'no implicit product wire')
    expected=[dict(kind='retained_scalar',raw_variables=[v],terms=[[1,[mp[v]]]])for v in keep]
    expected += [dict(kind='strict_common_V',raw_variables=[656],terms=[[1,[mp[656]]],[-1,[]]]),
                 dict(kind='paired_index_slacks',raw_variables=[674,861],terms=[[1,[n]]]if extra else[[1,[mp[674],mp[861]]]])]
    need(len(cert['guards'])==77,'complete guard certificate')
    for j,(g,p)in enumerate(zip(cert['guards'],expected)):
        a,b,c=range(n+extra+3*j,n+extra+3*j+3)
        need(g==dict(predicate=p,auxiliary=[a,b,c]),'every actual guard value and fresh triple')
        need(eq['variables'][a:c+1]==[dict(kind='nonnegative_guard',name='paired_guard.'+str(j)+'.'+s)for s in['a','b','c']],'all auxiliary metadata ownership')
        need(eq['residuals'][nr+extra+j]==dict(label='paired_guard.'+str(j),terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]),'complete quadratic guard polynomial')
    return dict(fixed_body_variables=n,fixed_body_rows=nr,guard_predicates=77,retained_scalar_guards=75,product_wires=extra)

def raw_compact_bijection(raw_eq,compact_eq,restore,mode,raw_rows):
    retained=restore['retained_raw_indices'];images={v:{(i,):1}for i,v in enumerate(retained)}
    for r in restore['omitted']:
        v=r['raw_variable'];need(v not in images,'unique raw affine recipe');images[v]=poly(r['terms'])
        need(all(len(m)<=1 and all(v<667 for v in m)for m in images[v]),'literal integer-affine source recipe')
    need(set(images)==set(range(1259)),'all1259 raw source recipes')
    # Forward implication: at a raw zero the omitted value must equal its
    # displayed recipe, by induction through the actual monic defining rows.
    # Checking only substitution identities would prove the reverse map.
    known=set(retained);defs={r['gate']:poly(r['terms'])for r in raw_rows if r.get('gate')is not None}
    for r in sorted(restore['omitted'],key=lambda r:r['raw_variable']):
        v=r['raw_variable'];q=defs[v];coefficient=q.get((v,),0)
        need(coefficient in[-1,1]and all(v not in m for m in q if m!=(v,)),'actual omitted definition is monic')
        need({i for m in q if m!=(v,)for i in m}<=known,'all forward restoration dependencies were already forced')
        need(not sub(q,images),'literal recipe is the unique solution of its actual defining row')
        known.add(v)
    need(known==set(range(1259)),'full triangular integer uniqueness, without sign assumptions')
    for v in range(1259,len(raw_eq['variables'])):images[v]={(v-592,):1}
    need(len(images)==len(raw_eq['variables']),'entire raw-parent inverse defined')
    for v in retained+list(range(1259,len(raw_eq['variables']))):
        i=retained.index(v)if v<1259 else v-592
        need(images[v]=={(i,):1},'restriction after restoration is identity')
    omit={r['raw_variable']for r in restore['omitted']};target=0;deleted=0
    for i,row in enumerate(raw_eq['residuals']):
        image=sub(poly(row['terms']),images)
        if i<1177 and raw_rows[i].get('gate')in omit:
            need(not image,'each deleted source defining row is an identity');deleted+=1
        else:
            need(image==poly(compact_eq['residuals'][target]['terms']) and row['label']==compact_eq['residuals'][target]['label'],'every surviving body/wire/guard row becomes literal compact row');target+=1
    need(deleted==592 and target==len(compact_eq['residuals']),'whole raw/compact row partition')
    return dict(unique_affine_restorations=592,forward_monic_uniqueness_rows=592,complete_raw_rows_checked=len(raw_eq['residuals']),literal_compact_rows=target,
                fresh_witnesses=0,sign_premises=0,mode=mode)

def product_wire_bijection(direct,wire,cert):
    n=cert['baseline_body_variables'];nr=cert['baseline_body_rows']
    row=poly(wire['residuals'][nr]['terms']);restored={m:-c for m,c in row.items()if m!=(n,)}
    need(row.get((n,))==1 and all(n not in m for m in restored),'monic independent product restoration')
    images={i:{(i if i<n else i-1,):1}for i in range(len(wire['variables']))if i!=n};images[n]=restored
    need(len(images)==len(wire['variables']),'entire one-wire inverse defined')
    target=0
    for i,r in enumerate(wire['residuals']):
        image=sub(poly(r['terms']),images)
        if i==nr:need(not image,'product definition becomes zero')
        else:
            need(image==poly(direct['residuals'][target]['terms'])and r['label']==direct['residuals'][target]['label'],'every remaining row is literally the direct-product row');target+=1
    need(target==len(direct['residuals']),'entire direct residual list reached')
    return dict(unique_product_restorations=1,complete_wire_rows_checked=len(wire['residuals']),copied_guard_triples=77,
                fresh_witnesses=0,sign_premises=0)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if (HERE/'MANIFEST.json').exists():
        seal=load(HERE/'MANIFEST.json')['files']
        need(set(seal)=={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()and p.name!='MANIFEST.json'},'closed profile file set')
        for n,h in seal.items():need(digest((HERE/n).read_bytes())==h,'closed profile member '+n)
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole source '+n)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['files'].items():need(digest((HERE/n).read_bytes())==h,'whole generated profile '+n)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    body=load(ROOT/'candidates/projected-radius-mixed-bounds/source/natural667.json')
    restore=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_restoration.json')
    old=load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    proof=load(ROOT/'research/paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json')
    need([raw['variables'][i]for i in restore['retained_raw_indices']]==body['variables'],'all compact metadata literally selected')
    base={};domains={};mutations=[]
    for family in['compact','raw']:
        for mode in['direct','wire']:
            name=family+'/'+mode;eq=load(HERE/name/'parent.json');cert=load(HERE/name/'domain.json');base[name]=eq
            domains[name]=domain(eq,cert,family,mode,raw,body,restore,old,proof)
            bad=deepcopy(eq);bad['residuals'][-2]['terms'][1][0]=0
            mutations.append(reject('remove actual V-1 bound '+name,lambda:domain(bad,cert,family,mode,raw,body,restore,old,proof)))
            bad=deepcopy(eq);bad['residuals'][-1]['terms'][0][0]=2
            mutations.append(reject('change paired predicate '+name,lambda:domain(bad,cert,family,mode,raw,body,restore,old,proof)))
    bridges={mode:raw_compact_bijection(base['raw/'+mode],base['compact/'+mode],restore,mode,raw['rows'])for mode in['direct','wire']}
    wire_bridges={family:product_wire_bijection(base[family+'/direct'],base[family+'/wire'],load(HERE/family/'wire/domain.json'))for family in['compact','raw']}
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole arithmetic archive')
    inverse=module('independent_signed_fixtures',ROOT/'candidates/projected-radius-integers/check.py')
    results={}
    with tempfile.TemporaryDirectory(prefix='paired-guard-independent-')as tmp,zipfile.ZipFile(archive)as z:
        for n,h in pins['members'].items():need(digest(z.read(n))==h,'pinned source member '+n)
        for n in['verify_projection.py','independent_polynomial.py','audit_common_radix.py']:
            member=next(m for m in pins['members']if m.endswith('/'+n));(Path(tmp)/n).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp));from verify_projection import verify
        census=load(HERE/'CENSUS.json')
        for name,record in census.items():
            eq=base['/'.join(name.split('/')[:2])];out=load(HERE/name/'equation.json');cert=load(HERE/name/'projection.json');p=load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed']==[],'every omitted integer uniquely restored')
            need(record['metrics']==out['metrics'],'literal metrics ledger')
            results[name]=dict(projection=verify(eq,out,cert),full_quartic=full_sos(out,p),
                               arbitrary_signed_restoration_fixtures=inverse.restoration_controls(eq,out,cert))
            if cert['steps']:
                bad=deepcopy(cert);bad['steps'][0]['restoration'][0][0]+=1
                mutations.append(reject('change signed inverse '+name,lambda:verify(eq,out,bad)))
            bad=deepcopy(p);bad['terms'][0][0]+=1
            mutations.append(reject('change full quartic '+name,lambda:full_sos(out,bad)))
    wire_matches=[]
    for name in results:
        if '/direct/' not in name or name.endswith('/unprojected')or name.endswith('/retained'):continue
        other=name.replace('/direct/','/wire/')
        a,b=load(HERE/name/'equation.json'),load(HERE/other/'equation.json')
        need(a['variables']==b['variables'],'actual matching projected metadata')
        def unsigned_row(r):
            p=poly(r['terms']);items=sorted(p.items());s=1 if not items or items[0][1]>0 else -1
            return tuple((m,s*c)for m,c in items)
        need(Counter(map(unsigned_row,a['residuals']))==Counter(map(unsigned_row,b['residuals'])),'exact projected residual multiset up to row signs')
        need(load(HERE/name/'polynomial.json')==load(HERE/other/'polynomial.json'),'every coefficient of matching direct/wire quartics')
        wire_matches.append(dict(direct=name,wire=other,literal_residual_lists_identical=a['residuals']==b['residuals'],
                                 residuals_permuted_up_to_sign=True,full_quartics_identical=True))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_domains=domains,raw_compact_bijections=bridges,
                product_wire_bijections=wire_bridges,identical_projected_direct_wire_pairs=wire_matches,profiles=results,rejected_corruptions=mutations,
                source_pins={str(p.relative_to(ROOT)):digest(p.read_bytes())for p in[HERE/'README.md',HERE/'SOURCE_PINS.json',HERE/'BUILD.json',Path(__file__)]},
                scope='Actual quadratic77-guard profiles, exact unrestricted-integer inverses before domain interpretation, complete quartics. Ordinary guard equivalence uses separately sealed paired-index proof. No global optimum, native/internal-ZFC or Lean claim.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),raw_compact_bijections=bridges),indent=2))

if __name__=='__main__':main()
