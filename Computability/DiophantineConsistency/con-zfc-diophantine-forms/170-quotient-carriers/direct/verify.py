#!/usr/bin/env python3
"""Independent literal edits, signed-power interface, maps and coefficients.

The retained independently written checker is used for Horn identities,
monic projection, translations and affine maps. No producing or searching
module is imported. These are finite checks, not an unbounded proof.
"""
from pathlib import Path
import argparse,copy,hashlib,json,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'baseline/direct'
sys.path.insert(0,str(BASE))
import check_factorial_free as C
sys.path.insert(0,str(ROOT))
import audit_power_interface as P

def raw_check(actual=None):
    oldpath=BASE/'factorial_free_affine/raw_source.json'
    C.need(C.hsh(oldpath)=='7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855','immutable factorial-free source')
    old=C.read(oldpath)
    expected=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    V=lambda n:C.var(names[n])
    t0=V('t0');F=V('crt.growth_majorant_F');R=names['mul.1']
    reps=[C.plus(V('crt.encoded.'+s),C.const(1)) for s in ['a','b','c','d','S','Sp','u','vq']]
    reps.append(C.plus(V('crt.encoded_index_minus_one'),C.const(1)))
    expected_changes={
      'cofinal.horizon':C.plus(t0,C.scale(C.times(V('cofinal.horizon_root'),V('cofinal.horizon_root')),-2)),
      'growth.base_definition':C.plus(V('growth.power_base'),C.scale(t0,-1),C.const(-16)),
      'radix.odd_square':C.plus(V('pow2.output'),C.scale(V('radix.odd_square_root_half'),-6),C.const(-3)),
      'self_radix.base_definition':C.plus(V('self_radix.BH'),C.scale(C.times(V('choose0.output'),C.plus(C.const(3),C.scale(C.plus(*reps),6))),-1)),
      'bootstrap.beta_base_square_product':C.plus(V('y'),C.scale(C.times(F,C.plus(C.const(1),C.scale(V('beta.odd_square_root_half'),2))),-1))}
    square_relation=C.plus(C.var(R),C.scale(C.times(F,F),-1))
    dropped=[];changed=[];rows=[]
    for i,row in enumerate(old['residuals']):
        p=C.poly(row['terms']);label=row['label']
        if label=='beta.odd_square_multiplier' or p==square_relation:
            dropped.append((i,label));continue
        rr=copy.deepcopy(row)
        if label in expected_changes:
            p=expected_changes[label];changed.append(label)
            if label=='radix.odd_square':rr['label']='radix.nonunit_affine'
        rr['terms']=C.terms(C.subst(p,R,F));rows.append(rr)
    C.need(len(dropped)==2 and sorted(changed)==sorted(expected_changes),'exact source edit inventory')
    expected['residuals']=rows
    expected['variant']='diagonal_growth_even_horizon_nonunit_affine_radix'
    for oldname,newname in [('growth.power_base','growth.diagonal_base'),('radix.odd_square_root_half','radix.odd_multiple_of_three_parameter'),('beta.odd_square_root_half','beta.odd_multiplier_parameter')]:
        expected['variables'][names[oldname]]['name']=newname
    actual=actual if actual is not None else C.read(ROOT/'diagonal_raw/raw_source.json')
    C.need(expected==actual,'complete independent source reconstruction')
    C.need(all(C.degree(C.poly(r['terms']))<=2 for r in actual['residuals']),'quadratic raw source')
    C.need(not any(R in m for row in actual['residuals'] for _,m in row['terms']),'binomial shift alias is global')
    sb=names['beta.odd_square_multiplier']
    C.need(not any(sb in m for row in actual['residuals'] for _,m in row['terms']),'deleted beta wire is private')
    return actual,{'changed_rows':len(changed),'deleted_rows':len(dropped),'global_alias':'old binomial shift R -> F'}

def negative_controls(raw):
    rejected=[]
    def bad(name,fn):
        try:fn()
        except (ValueError,KeyError,IndexError):rejected.append(name);return
        raise ValueError('Accepted corrupted artifact: '+name)
    for label in ['cofinal.horizon','growth.base_definition','radix.nonunit_affine','self_radix.base_definition','bootstrap.beta_base_square_product','shared.frame_definition']:
        d=copy.deepcopy(raw);row=next(r for r in d['residuals'] if r['label']==label)
        row['terms'][0][0]+=1
        bad(label,lambda d=d:raw_check(d))
    cert=C.read(ROOT/'diagonal238/certificate.json');wrong=copy.deepcopy(cert)
    wrong['projections'][0]['replacement'][0][0]+=1
    bad('affine restoration',lambda:C.affine_check(C.read(ROOT/'diagonal_raw/equation.json'),ROOT/'diagonal238',wrong))
    expanded=C.read(ROOT/'diagonal238/expanded_polynomial.json');wrong=copy.deepcopy(expanded)
    wrong['terms'][0][0]+=1
    bad('collected quartic coefficient',lambda:C.quartic_check(ROOT/'diagonal238',expanded=wrong))
    return rejected

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);ap.add_argument('--skip-parent',action='store_true')
    args=ap.parse_args()
    inherited=None
    if not args.skip_parent:
        run=subprocess.run([sys.executable,'-B',str(BASE/'check_factorial_free.py'),'--affine-only'],check=True,capture_output=True,text=True)
        inherited=json.loads(run.stdout)
    raw,delta=raw_check()
    power=P.audit(ROOT/'diagonal_raw/raw_source.json')
    maps=C.projection_check(ROOT/'diagonal_raw',raw)
    profiles={'diagonal_raw':{'metrics':C.quartic_check(ROOT/'diagonal_raw')}}
    for name in ['diagonal239','diagonal238','diagonal239_balanced','diagonal238_balanced']:
        folder=ROOT/name
        profiles[name]={'maps':C.affine_check(C.read(ROOT/'diagonal_raw/equation.json'),folder),'metrics':C.quartic_check(folder)}
    for n in [239,238]:
        name='diagonal'+str(n)+'_centered';folder=ROOT/name
        tr=C.read(folder/'translation_certificate.json')
        C.need(tr['source']=='diagonal'+str(n)+'_balanced' and tr['convention']=='old=new+shift','centered source/convention')
        source=C.read(ROOT/tr['source']/'equation.json');eq=C.read(folder/'equation.json')
        C.need(eq['variables']==source['variables'] and len(eq['residuals'])==len(source['residuals']),'centered census')
        for oldrow,newrow in zip(source['residuals'],eq['residuals']):
            p=C.poly(oldrow['terms'])
            for v,d in tr['shifts']:
                C.need(type(v) is int and type(d) is int,'integral translation')
                p=C.subst(p,v,C.plus(C.var(v),C.const(d)))
            C.need(p==C.poly(newrow['terms']),'exact centered residual')
        profiles[name]={'integer_translations':len(tr['shifts']),'metrics':C.quartic_check(folder)}
        reduced='diagonal'+str(n)+'_reduced';rf=ROOT/reduced;rc=C.read(rf/'row_certificate.json')
        C.need(rc['source']==name,'reduced source')
        rows=[C.poly(row['terms']) for row in eq['residuals']]
        for i,j,k in rc['operations']:
            C.need(i!=j and type(k) is int,'invertible final row operation')
            rows[i]=C.plus(rows[i],C.scale(rows[j],k))
        out=C.read(rf/'equation.json')
        C.need(out['variables']==eq['variables'] and rows==[C.poly(row['terms']) for row in out['residuals']],'exact reduced rows')
        profiles[reduced]={'integer_row_operations':len(rc['operations']),'metrics':C.quartic_check(rf)}
    result={'status':'PASS','new_source':delta,'power_interface':power,'initial_projection':maps,'profiles':profiles,
      'rejected_corruptions':negative_controls(raw),'inherited_exact_source_audit':inherited,
      'scope':'Independent complete source edits, every retained power request/frame atom, Horn factoring, all monic and affine maps, and complete coefficient collection. Unbounded proof and calibration are separate.'}
    output=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(output)
    print(output,end='')

if __name__=='__main__':main()
