#!/usr/bin/env python3
"""Independent complete finite check of the 306-coordinate transformation.

This verifier does not import build.py. It verifies algebra and artifact
bindings, not unbounded Pell number theory or consistency by enumeration.
"""
from pathlib import Path
import collections
import copy
import hashlib
import json
import argparse

ROOT=Path(__file__).resolve().parent
EXPECTED_BLOBS={
 'integer324-equation.json':'4e81e3183b8bb3a9ba7d8114adf8a1a29ee80f87',
 'integer324-translation-certificate.json':'fcd0efb97ddbd32c77af4a97aa5bd0476a312276',
 'PROOF_324.md':'56e57e960370aceda837ff5e875d6f79ce408606',
 'cap-projection-certificate.json':'129c186622620b44ce50c465ef3aa051de258bbc',
 'cap-source.json':'2881d6ad6e38d65ca29523855c33bb13ac189a9c',
 'cap-transform-certificate.json':'3889b3c499e9f2e64901164b85e3048a20bfbb49'}

def require(ok,where):
    if not ok:
        raise ValueError(where)

def canonical(x):
    return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()

def chash(x):
    return hashlib.sha256(canonical(x)).hexdigest()

def read(p):
    return json.loads(p.read_text())

def coefficients(ts):
    d=collections.defaultdict(int)
    for c,m in ts:
        require(type(c) is int and all(type(i) is int for i in m),'integer coefficient/index')
        d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}

def add(p,q):
    d=collections.defaultdict(int,p)
    for m,c in q.items():d[m]+=c
    return {m:c for m,c in d.items() if c}

def mul(p,q):
    d=collections.defaultdict(int)
    for m,a in p.items():
        for n,b in q.items():d[tuple(sorted(m+n))]+=a*b
    return {m:c for m,c in d.items() if c}

def minus(p):return {m:-c for m,c in p.items()}
def v(i):return {(i,):1}

def validate(parent,translation,new,cert,expanded,claimed):
    count=0
    def check(ok,where):
        nonlocal count
        require(ok,where);count+=1
    check(len(parent['variables'])==324 and len(parent['residuals'])==208,'parent size')
    check(new['domain']=='unrestricted integers','integer domain')
    check(len(new['variables'])==306 and len(new['residuals'])==206,'output size')
    check(cert['parent_canonical_sha256']==chash(parent),'canonical parent binding')
    check(cert['output_canonical_sha256']==chash(new),'canonical output binding')
    removed=list(range(252,279))
    oldrows=list(range(184,193))
    keep=[i for i in range(324) if i not in removed]
    ren={i:j for j,i in enumerate(keep)}
    check(cert['removed_parent_variables']==removed,'all removed variables')
    check(cert['removed_parent_rows']==oldrows,'all removed rows')
    check(cert['retained_parent_variables']==keep,'complete surviving coordinate map')
    check(new['variables'][:297]==[parent['variables'][i] for i in keep],'surviving metadata')
    shifts=dict(translation['shifts'])
    check(translation['convention']=='old=new+shift','translation convention')
    check(translation['output_sha256']==chash(parent),'parent centering binding')
    request=[[1,[10]],[-1,[]]]
    factors=[{(10,):1,():-1}]+[v(i) for i in range(11,18)]
    expected_names=['a','b','c','d','S','Sp','u','vq']
    for j,i in enumerate(range(10,18)):
        check(parent['variables'][i]['name']=='crt.encoded.'+expected_names[j],'request name')
        check(shifts.get(i,0)==(-2 if j==0 else -1),'request affine shift')
    check(parent['variables'][18]['name']=='crt.encoded_index_minus_one','reciprocal index')
    check(shifts[18]==-1,'reciprocal index shift')
    xs=[174,180,184,188,192,200,204,212,216]
    xnames=['index3.X','index5.X','index6.X','index7.X','index8.X',
            'index10.X','index11.X','index13.X','index14.X']
    for i,n in zip(xs,xnames):
        check(parent['variables'][i]['name']==n and shifts.get(i,0)==0,'abscissa chart')
    check(cert['selected_parent_abscissas']==xs,'selected abscissa certificate')
    orientation={():9,**{(i,):-1 for i in xs}}
    check(coefficients(cert['orientation_parent_terms'])==orientation,'linear orientation')
    check(cert['private_pool_quotient_parent_index']==242,'quotient certificate')
    q_occ=[j for j,r in enumerate(parent['residuals'])
           if any(242 in m for c,m in r['terms'])]
    check(parent['variables'][242]['name']=='cap.pooled_quotient' and q_occ==[180],
          'complete quotient privacy')
    check(parent['variables'][151]['name']=='shared.A' and shifts[151]==1,'A chart')
    for j,g in enumerate(range(3,12)):
        row=184+j
        ids=list(range(252+3*j,255+3*j))
        raw_coord=10+j
        offset=-2 if j==0 else -1
        expected={(raw_coord,):1,():offset,(ids[0],ids[0]):-1,
                  (ids[1],ids[1]):-1,(ids[2],ids[2]):-1,(ids[2],):-1}
        check(parent['residuals'][row]['label']==f'domain_guard.{g}','removed graph label')
        check(coefficients(parent['residuals'][row]['terms'])==expected,'whole deleted graph')
        for i,a in zip(ids,'abc'):
            occurrences=[k for k,r in enumerate(parent['residuals'])
                         if any(i in m for c,m in r['terms'])]
            check(parent['variables'][i]['name']==f'guard{g}.{a}' and occurrences==[row],
                  'complete deleted witness privacy')
    retained=[i for i in range(208) if i not in oldrows]
    check(cert['retained_row_map']==[[i,j] for j,i in enumerate(retained)],'whole row map')
    check(cert['pool_parent_row']==180 and cert['pool_output_row']==180,'pool row map')
    for j,i in enumerate(retained):
        p=coefficients(parent['residuals'][i]['terms'])
        if i==180:
            check(parent['residuals'][i]['label']=='cap.pooled_index_residue','pool label')
            check(p.get((151,242))==-1,'literal pool divisor and quotient')
            p=add(p,orientation)
        transformed={tuple(ren[k] for k in m):c for m,c in p.items()}
        check(new['residuals'][j]['label']==parent['residuals'][i]['label'],'retained row label')
        check(coefficients(new['residuals'][j]['terms'])==transformed,'complete retained row equality')
    check(cert['product_output_variables']==list(range(297,303)),'product coordinates')
    check(cert['strict_product_output_triple']==[303,304,305],'triple coordinates')
    check([coefficients(x) for x in cert['requested_eight_output_terms']]==factors,'factor chart')
    acc=factors[0]
    for j,i in enumerate(range(297,303)):
        expected=add(v(i),minus(mul(acc,factors[j+1])))
        check(coefficients(new['residuals'][199+j]['terms'])==expected,'complete monic product')
        check(new['residuals'][199+j]['label']==f'orientation.product_{j+2}','product label')
        check(new['variables'][i]=={'name':f'orientation.P{j+2}','kind':'gate'},'product metadata')
        acc=v(i)
    fused=add(mul(acc,factors[7]),{():-1,(303,303):-1,(304,304):-1,(305,305):-1,(305,):-1})
    check(coefficients(new['residuals'][205]['terms'])==fused,'whole fused product graph')
    check(new['residuals'][205]['label']=='orientation.fused_strict_product','fused graph label')
    expected_poly={}
    for r in new['residuals']:
        p=coefficients(r['terms'])
        check(max(map(len,p),default=0)<=2,'quadratic residual')
        check(all(0<=i<306 for m in p for i in m),'valid full coordinate range')
        expected_poly=add(expected_poly,mul(p,p))
    check(expanded['variables']==306,'expanded coordinate count')
    check(coefficients(expanded['terms'])==expected_poly,'every collected coefficient')
    metrics={'variables':306,'residuals':206,'degree':max(map(len,expected_poly)),
             'monomials':len(expected_poly),'coefficient_height':max(map(abs,expected_poly.values())),
             'residual_height':max(abs(c) for r in new['residuals'] for c,m in r['terms'])}
    check(metrics==claimed,'all exact metrics')
    check(metrics=={'variables':306,'residuals':206,'degree':4,'monomials':6259,
                   'coefficient_height':128446,'residual_height':256},'frozen expected metrics')
    return {'checks':count,'metrics':metrics,'equation_sha256':chash(new),
            'expansion_sha256':chash(expanded)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    a=parser.parse_args()
    provenance=[]
    for name,wanted in EXPECTED_BLOBS.items():
        b=(ROOT/'parent'/name).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(actual==wanted,'pinned Git blob '+name)
        provenance.append({'file':name,'git_blob_sha1':actual,'sha256':hashlib.sha256(b).hexdigest()})
    parent=read(ROOT/'parent/integer324-equation.json')
    trans=read(ROOT/'parent/integer324-translation-certificate.json')
    equation=read(ROOT/'integer306/equation.json')
    cert=read(ROOT/'integer306/transformation_certificate.json')
    expanded=read(ROOT/'integer306/expanded_polynomial.json')
    metrics=read(ROOT/'integer306/METRICS.json')
    report=validate(parent,trans,equation,cert,expanded,metrics)
    mutations=[]
    for mode in ['wrong_orientation','wrong_factor_shift','quotient_escape','wrong_collected_coefficient']:
        p=copy.deepcopy(parent);e=copy.deepcopy(equation);c=copy.deepcopy(cert);x=copy.deepcopy(expanded)
        if mode=='wrong_orientation':
            e['residuals'][180]['terms'].append([1,[174]])
            c['output_canonical_sha256']=chash(e)
        elif mode=='wrong_factor_shift':
            e['residuals'][199]['terms'].append([1,[11]])
            c['output_canonical_sha256']=chash(e)
        elif mode=='quotient_escape':
            p['residuals'][0]['terms'].append([1,[242]])
            c['parent_canonical_sha256']=chash(p)
            trans1=copy.deepcopy(trans);trans1['output_sha256']=chash(p)
        else:
            x['terms'][0][0]+=1
        try:
            validate(p,trans1 if mode=='quotient_escape' else trans,e,c,x,metrics)
        except ValueError as exc:
            mutations.append({'mutation':mode,'rejected':True,'reason':str(exc)})
        else:
            raise ValueError('corruption escaped: '+mode)
    report['parent_git_bindings']=provenance
    report['negative_controls']=mutations
    report['scope']='Complete finite transformation, privacy, coefficient and metric checks; ordinary unbounded proof is separate.'
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(canonical(report))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
