#!/usr/bin/env python3
"""Independent finite audit of the 245-integer quartic.

No producing compiler, eliminator, or translation module is imported. The
retained independent algebra module supplies exact sparse arithmetic and
certificate replay. The ordinary proof establishes the unbounded semantics.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / 'inherited' / 'normalized252'
sys.path.insert(0, str(PARENT / 'code'))
import inherited_independent_algebra as A


def get(p):
    return json.loads(p.read_text())


def check_pins():
    pins=get(ROOT/'SOURCE_PINS.json')
    for entry in pins['parent_files']:
        path=ROOT/entry['path']
        data=path.read_bytes()
        A.need(len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],
               'Inherited source pin mismatch: '+entry['path'])
    for name,key in [('equation/equation.json','new_equation_sha256'),
                     ('equation/expanded_polynomial.json','new_expanded_polynomial_sha256')]:
        A.need(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==pins[key],
               'Release endpoint pin mismatch: '+name)
    return len(pins['parent_files'])


def audit_source(parent, old_tf, new, cert):
    A.need(A.sha(parent)==cert['parent_guarded_sha256'],'parent source digest')
    A.need(A.sha(old_tf)==cert['parent_remainder_transform_sha256'],'parent transform digest')
    A.need(A.sha(new)==cert['source_sha256'],'new source digest')
    names = {v['name']:i for i,v in enumerate(parent['variables'])}
    f,b,out,r,s = [names[n] for n in ('fact0.output','choose0.output','pow0.output','fact0.remainder','fact0.slack')]
    m = names['pow14.output']
    guard = [g for g in old_tf['new_guards'] if g['kind']=='front_nonnegative']
    A.need({g['coordinate'] for g in guard}=={r,s,names['choose0.oslack']} and len(guard)==3,'front guard set')
    removed = set()
    for g in guard:
        aa,bb,cc = g['auxiliary']
        expected = A.add(A.v(g['coordinate']),{(aa,aa):-1,(bb,bb):-1,(cc,cc):-1,(cc,):-1})
        A.need(A.norm(parent['residuals'][g['row']])==expected,'front guard exact ternary expression')
        removed.add(g['row'])
    labels = {label:[i for i,row in enumerate(parent['residuals']) if row['label']==label]
              for label in ('fact0.ceiling','fact0.remainder_bound','self_radix.base_definition')}
    A.need(all(len(x)==1 for x in labels.values()),'semantic row census')
    ci,bi = labels['fact0.ceiling'][0],labels['fact0.remainder_bound'][0]
    cpoly,bpoly = A.norm(parent['residuals'][ci]),A.norm(parent['residuals'][bi])
    prod = names['mul.5']
    product = A.add(A.v(prod),A.sc(A.mul(A.v(f),A.v(b)),-1))
    products = [i for i,row in enumerate(parent['residuals']) if A.norm(row)==product]
    A.need(len(products)==1,'unique old ceiling product')
    pi=products[0]
    A.need(A.add(cpoly,A.sc(bpoly,-1),product)==A.add(A.v(out),A.v(s),A.sc(A.mul(A.v(f),A.v(b)),-1)),
           'old ceiling really gives FB=V+s')
    A.need(bpoly==A.add(A.v(b),A.sc(A.v(r),-1),A.sc(A.v(s),-1),A.con(-1)),'old interval relation')
    removed.update((ci,bi,pi))
    A.need(sorted(removed)==[x['row'] for x in cert['removed_rows']],'deletion row identifiers')
    A.need(all(parent['residuals'][x['row']]==x['content'] for x in cert['removed_rows']),'deleted row bytes')
    A.need(cert['removed_guards']==guard,'deleted guard records')
    expected=copy.deepcopy(parent)
    expected['residuals']=[row for i,row in enumerate(parent['residuals']) if i not in removed]
    ratio,slack=len(parent['variables']),len(parent['variables'])+1
    expected['variables'] += [
        {'name':'ceiling.ratio','kind':'signed_witness'},
        {'name':'ceiling.normalized_slack','kind':'signed_witness'},
    ]
    ratio_poly=A.add(A.v(m),A.sc(A.mul(A.v(b),A.v(ratio)),-1))
    scaled_poly=A.add(A.mul(A.v(f),A.v(m)),A.sc(A.mul(A.v(ratio),A.v(out)),-1),A.sc(A.v(slack),-1))
    # An independent symbolic check of the exact normalization identity.
    A.need(A.add(scaled_poly,A.sc(A.mul(A.v(f),ratio_poly),-1))==
           A.add(A.mul(A.v(ratio),A.add(A.mul(A.v(f),A.v(b)),A.sc(A.v(out),-1))),A.sc(A.v(slack),-1)),
           'normalized ceiling syzygy')
    added=[{'label':'ceiling.common_ratio','terms':A.terms(ratio_poly)},
           {'label':'ceiling.scaled_identity','terms':A.terms(scaled_poly)}]
    A.need(cert['added_rows']==added,'new ceiling rows')
    A.need(cert['added_variables']==[[ratio,expected['variables'][ratio]],[slack,expected['variables'][slack]]],
           'new ceiling coordinates')
    expected['residuals'] += added
    radix=parent['residuals'][labels['self_radix.base_definition'][0]]
    radix_p=A.norm(radix)
    rhs_gates=[mon[0] for mon,c in radix_p.items() if len(mon)==1 and c==1]
    A.need(len(rhs_gates)==1,'unique BH gate')
    bh=rhs_gates[0]
    reps=[names['crt.encoded.'+x] for x in ('a','b','c','d','S','Sp','u','vq')]+[names['crt.encoded_index_minus_one']]
    sum_actual=A.add(A.con(9),*[A.v(i) for i in reps])
    old_h=A.add(A.con(1),sum_actual)
    new_h=A.add(A.con(1),A.sc(sum_actual,2))
    A.need(radix_p==A.add(A.v(bh),A.sc(A.mul(A.v(b),old_h),-1)),'old source H identity')
    new_radix=dict(radix,terms=A.terms(A.add(A.v(bh),A.sc(A.mul(A.v(b),new_h),-1))))
    # H is identically odd even when every actual representative is signed.
    A.need(new_h.get((),0)%2==1 and all(c%2==0 for mon,c in new_h.items() if mon),'odd H coefficient identity')
    frame=[row for row in parent['residuals'] if row['label']=='shared.frame_definition']
    A.need(len(frame)==1 and A.norm(frame[0]).get((bh,bh))==-1,'new BH still in unchanged square frame')
    g=old_tf['new_guards'][-1]
    A.need(g['kind']=='centered_remainder_budget','common remainder guard order')
    sphere=parent['residuals'][g['row']]
    rems=[i for group in old_tf['new_groups'] for i in group['remainders']]
    A.need(len(rems)==11 and len(set(rems))==11,'eleven old normalized remainders')
    aa,bb,cc=g['auxiliary']
    base_sphere=A.add(A.mul(A.v(m),A.v(m)),A.con(-1),
                      A.sc(A.add(*[A.mul(A.v(i),A.v(i)) for i in rems]),-4),
                      {(aa,aa):-1,(bb,bb):-1,(cc,cc):-1,(cc,):-1})
    A.need(A.norm(sphere)==base_sphere,'old sphere exact literal equation')
    new_sphere=dict(sphere,terms=A.terms(A.add(base_sphere,{(slack,slack):-4})))
    edits=[]
    for i,row in enumerate(expected['residuals']):
        if row==radix:
            expected['residuals'][i]=new_radix
            edits.append({'kind':'odd_nonzero_radix_multiplier','old':row,'new':new_radix})
        elif row==sphere:
            expected['residuals'][i]=new_sphere
            edits.append({'kind':'add_normalized_ceiling_to_norm','old':row,'new':new_sphere})
    A.need(edits==cert['row_edits'],'exact source edit ledger')
    expected['variant']+=':odd_multiplier_and_normalized_rounded_ceiling'
    A.need(expected==new,'entire new source reconstructed independently')
    A.need(cert['semantic_coordinates']=={'F':f,'B':b,'V':out,'M':m,'vB':ratio,'S':slack,'old_r':r,'old_s':s,'base_BH':bh},
           'semantic coordinate ledger')
    A.need(cert['representatives']==[{'stored':i,'actual_shift':1} for i in reps],'nine representative coordinate ledger')
    return {'removed_front_guards':3,'normalized_remainders_including_ceiling':12,'added_coordinates':2,'removed_rows':6,'added_rows':2}


def audit(data,end,override=None):
    data_files={p.stem:get(p) for p in data.glob('*.json')}
    end_files={p.stem:get(p) for p in end.glob('*.json')}
    if override:
        group,name,value=override
        (data_files if group=='data' else end_files)[name]=value
    parent=get(PARENT/'data/guarded.json')
    old_tf=get(PARENT/'data/remainder_transformation.json')
    source_result=audit_source(parent,old_tf,data_files['source'],data_files['source_transformation'])
    src=data_files['source'];fac=data_files['factored_source'];projected=data_files['projected']
    edits=A.factorization(src,fac,data_files['factorization_certificate'])
    nsteps=A.projection(fac,projected,data_files['projection_certificate'])
    A.need(end_files['projected']==projected,'final endpoint projection boundary')
    final=end_files['equation'];tr=end_files['translation_certificate']
    A.need(A.sha(projected)==tr['input_sha256'] and A.sha(final)==tr['output_sha256'],'translation digests')
    A.need(tr['convention']=='old=new+shift','translation convention')
    shifts=dict(tr['shifts'])
    A.need(len(shifts)==len(tr['shifts']),'duplicate coordinate shift')
    A.need(all(type(i) is int and 0<=i<len(projected['variables']) and type(v) is int for i,v in shifts.items()),'integer shift map')
    A.need(final['variables']==projected['variables'],'translation variable list')
    A.need(len(final['residuals'])==len(projected['residuals']),'translation row census')
    for old,new in zip(projected['residuals'],final['residuals']):
        poly=A.norm(old)
        for i,shift in shifts.items():
            poly=A.sub(poly,i,A.add(A.v(i),A.con(shift)))
        A.need(old['label']==new['label'] and poly==A.norm(new),'literal integral translation')
    expanded,used=A.literal(final)
    A.need(used==set(range(len(final['variables']))),'every final coordinate is live')
    A.need(expanded==A.norm(end_files['expanded_polynomial']),'complete independently collected quartic')
    metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':A.deg(expanded),
             'monomials':len(expanded),'height':max(map(abs,expanded.values())),
             'row_height':max(abs(c) for row in final['residuals'] for c,mon in row['terms'])}
    A.need(metrics=={k:end_files['METRICS'][k] for k in metrics},'exact final metrics')
    return {'status':'PASS','source_reconstruction':source_result,'horn_factorization_edits':edits,
            'monic_projection_steps':nsteps,'integer_translation':True,'complete_quartic_expansion':True,
            'metrics':metrics,'equation_sha256':A.sha(final),'expanded_sha256':A.sha(end_files['expanded_polynomial'])}


def corruptions(data,end):
    cases=[]
    for label,field in [('omit normalized ceiling square','sphere'),('wrong odd multiplier constant','radix'),
                        ('wrong ceiling ratio sign','ratio'),('wrong scaled ceiling product','ceiling')]:
        src=get(data/'source.json');cert=get(data/'source_transformation.json')
        if field=='sphere':
            sid=cert['semantic_coordinates']['S']
            row=next(r for r in src['residuals'] if r['label']=='domain_guard.4')
            row['terms']=[t for t in row['terms'] if t[1]!=[sid,sid]]
        else:
            row=next(r for r in src['residuals'] if r['label']=={'radix':'self_radix.base_definition','ratio':'ceiling.common_ratio','ceiling':'ceiling.scaled_identity'}[field])
            row['terms'][0][0]+=1
        cert['source_sha256']=A.sha(src)
        try:
            audit_source(get(PARENT/'data/guarded.json'),get(PARENT/'data/remainder_transformation.json'),src,cert)
        except ValueError:
            cases.append(label)
        else:
            raise ValueError('Corruption accepted: '+label)
    expanded=get(end/'expanded_polynomial.json')
    expanded['terms'][0][0]+=1
    try:
        audit(data,end,('end','expanded_polynomial',expanded))
    except ValueError:
        cases.append('wrong expanded coefficient')
    else:
        raise ValueError('Expanded coefficient corruption accepted')
    cert=get(data/'projection_certificate.json')
    cert['steps'][0]['restoration'][0][0]+=1
    try:
        audit(data,end,('data','projection_certificate',cert))
    except ValueError:
        cases.append('wrong monic restoration')
    else:
        raise ValueError('Monic restoration corruption accepted')
    return cases


def rebuild():
    flags=['-B']+(['-O'] if sys.flags.optimize else [])
    with tempfile.TemporaryDirectory(prefix='rounded245_rebuild_') as td:
        fresh=Path(td);d=fresh/'data';e=fresh/'equation'
        for cmd in ([sys.executable,*flags,str(ROOT/'code/build.py'),'--output',str(d)],
                    [sys.executable,*flags,str(PARENT/'code/center_integer.py'),str(d),str(e)]):
            run=subprocess.run(cmd,capture_output=True,text=True)
            A.need(run.returncode==0,'Rebuild command failed: '+run.stdout+'\n'+run.stderr)
        count=0
        for folder,stored in ((d,ROOT/'data'),(e,ROOT/'equation')):
            first=sorted(p.name for p in folder.glob('*.json'));second=sorted(p.name for p in stored.glob('*.json'))
            A.need(first==second,'Rebuild JSON file census')
            for name in first:
                A.need((folder/name).read_bytes()==(stored/name).read_bytes(),'Rebuild byte mismatch '+name)
                count+=1
        audit(d,e)
        return {'byte_identical_json_files':count,'fresh_audit':'PASS'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--data',type=Path,default=ROOT/'data')
    ap.add_argument('--endpoint',type=Path,default=ROOT/'equation')
    ap.add_argument('--rebuild',action='store_true')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    result=audit(args.data,args.endpoint)
    result['pinned_inherited_files']=check_pins()
    result['negative_controls_rejected']=corruptions(args.data,args.endpoint)
    result['optimized_python']=bool(sys.flags.optimize)
    result['scope']='Finite source, Horn factoring, integral monic projection, integer chart and full SOS coefficient replay. No producer modules imported; unbounded semantics are proved separately.'
    if args.rebuild:
        A.need(args.data==ROOT/'data' and args.endpoint==ROOT/'equation','Rebuild uses sealed default endpoints')
        result['rebuild']=rebuild()
    text=json.dumps(result,indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(text)
    print(text,end='')


if __name__=='__main__':
    main()
