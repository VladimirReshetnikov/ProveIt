#!/usr/bin/env python3
"""Portable independent verification of the balanced 214-variable companion.

Uses adjacent verify_growth.py's independent sparse operations and preserved
independent projection checker. Does not import either construction program.
"""
from pathlib import Path
import argparse,copy,hashlib,json,tempfile
import verify_growth as v


def check_source(parent,source):
    old=json.loads(parent.read_text());new=v.read_eq(source)
    v.need(old.get('domain')==new.get('domain')=='unrestricted integers','balanced source domain')
    v.need(old['variables'][194]['name']=='self_radix.BH','old base coordinate binding')
    v.need(old['variables'][2]['name']=='growth.F','growth F binding')
    v.need(old['variables'][17]['name']=='crt.even_index_half','even index binding')
    # Uncontracted coordinates: F=x2, C=2*x17, B=x4. The historical
    # a representative is x9-1; all seven remaining representatives
    # occupy x10,...,x16. These offsets matter in the original base.
    original={(194,):1,(4,):2,(4,17):-8}
    for i in range(9,17):original[(4,i)]=-4
    removed=[i for i,r in enumerate(old['residuals']) if r['label']=='self_radix.base_definition']
    v.need(len(removed)==1 and v.p(old['residuals'][removed[0]]['terms'])==original,'old base polynomial binding')
    replacement={():2,(2,):2,(17,):4}
    expected=[];changed=[]
    for i,row in enumerate(old['residuals']):
        if i in removed:continue
        before=v.p(row['terms']);after=v.repl(before,194,replacement)
        expected.append((row['label'],after))
        if before!=after:changed.append(row['label'])
    v.need(changed==['base2.T_definition','multiplication','shared.frame_definition'],'actual changed interfaces')
    # Explicit retained multiple of B, independent of the deleted base row.
    divisibility={():1,(2,):1,(4,19):-1,(17,):2}
    v.need(sum(v.p(r['terms'])==divisibility for r in old['residuals'])==1,'CRT index divisibility absent')
    live=sorted({i for _,row in expected for mon in row for i in mon});ren={i:j for j,i in enumerate(live)}
    v.need(194 not in live,'base coordinate survived')
    v.need(new['variables']==[old['variables'][i] for i in live],'balanced variable table')
    v.need(len(new['residuals'])==len(expected),'balanced source residual count')
    for k,((label,row),target) in enumerate(zip(expected,new['residuals'])):
        target_poly={tuple(ren[i] for i in mon):c for mon,c in row.items()}
        v.need(label==target['label'] and target_poly==v.p(target['terms']),'balanced semantic delta row '+str(k))
        v.need(max(map(len,target_poly),default=0)<=2,'balanced source nonquadratic residual')
    cert=json.loads((source/'certificate.json').read_text())
    v.need(cert['input_sha256']==hashlib.sha256(parent.read_bytes()).hexdigest(),'balanced parent hash binding')
    v.need(cert['eliminated_coordinate']==194 and cert['deleted_rows']==removed,'balanced certificate removed interface')
    v.need(v.p(cert['replacement_original_coordinates'])==replacement,'balanced certificate affine base')
    v.need(cert['old_to_new']==[[i,j] for i,j in ren.items()],'balanced certificate renumbering')
    measured=v.verify_expansion(source,new)
    return {'status':'PASS','parent_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),
        'source_sha256':hashlib.sha256((source/'equation.json').read_bytes()).hexdigest(),
        'deleted_base_coordinate':194,'actual_changed_interfaces':changed,'metrics':measured}


def source_mutations(parent,source):
    eq=v.read_eq(source);exp=json.loads((source/'expanded_polynomial.json').read_text())
    met=json.loads((source/'metrics.json').read_text());cert=json.loads((source/'certificate.json').read_text())
    results=[]
    with tempfile.TemporaryDirectory(prefix='conzfc-balanced-corruption-') as name:
        temp=Path(name)
        for title,kind in [('changed affine radix in the main frame','frame'),('changed radix modulus','modulus'),
                           ('changed collected polynomial','expansion'),('false certificate replacement','certificate')]:
            bad=copy.deepcopy(eq);badexp=copy.deepcopy(exp);badcert=copy.deepcopy(cert)
            if kind=='frame':next(r for r in bad['residuals'] if r['label']=='shared.frame_definition')['terms'][0][0]*=-1
            elif kind=='modulus':next(r for r in bad['residuals'] if r['label']=='base2.T_definition')['terms'][0][0]*=-1
            elif kind=='expansion':badexp['terms'][0][0]*=-1
            else:badcert['replacement_original_coordinates'][0][0]*=-1
            for path,obj in [('equation.json',bad),('expanded_polynomial.json',badexp),('metrics.json',met),('certificate.json',badcert)]:v.write_json(temp/path,obj)
            try:check_source(parent,temp)
            except ValueError as err:results.append({'mutation':title,'rejected':True,'reason':str(err)})
            else:raise ValueError('Balanced corruption accepted: '+title)
    return results


def check(parent,source,radical,affine,optimized,projection_helper,mutations=True):
    parent,source,radical,affine,optimized,projection_helper=map(Path,
        (parent,source,radical,affine,optimized,projection_helper))
    source_receipt=check_source(parent,source)
    chain=v.check_chain(source,radical,affine,optimized,projection_helper,mutations,require_affine_hashes=False)
    result={'status':'PASS','source':source_receipt,'projection_and_optimization':chain,
       'scope':'Exact balanced source delta, five integral projections, affine consequence, integer chart operations and their composed inverse, all collected coefficients. Semantic radix proof and inherited calibration remain separate dependencies.'}
    if mutations:result['source_mutations']=source_mutations(parent,source)
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    for key in ['parent','source','radical','affine','optimized','projection-helper']:ap.add_argument('--'+key,type=Path,required=True)
    ap.add_argument('--no-mutations',action='store_true');ap.add_argument('--receipt',type=Path)
    a=ap.parse_args();res=check(a.parent,a.source,a.radical,a.affine,a.optimized,a.projection_helper,not a.no_mutations)
    rendered=json.dumps(res,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(rendered)
    print(rendered,end='')
