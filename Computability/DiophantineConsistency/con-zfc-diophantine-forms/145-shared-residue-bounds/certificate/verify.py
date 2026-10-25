#!/usr/bin/env python3
"""Independent exact audit of symmetric residue pooling and all final coefficients.

No producing compiler, optimizer or coordinate-search code is imported.
The algebra kernel and old-source auditor are retained independent checkers.
These finite checks do not decide consistency or replace the unbounded proof.
"""
from pathlib import Path
import argparse, copy, hashlib, json, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'parent'))
import round15_independent_algebra as P
import check_compiled_cap as C
need=P.need

CASES=[
 ('choose0.remainder','choose0.rslack','choose0.remainder_bound','pow4.output'),
 ('range0.remainder','range0.slack','crt.range.a.remainder_bound','pow6.output'),
 ('range1.remainder','range1.slack','crt.range.b.remainder_bound','pow6.output'),
 ('range2.remainder','range2.slack','crt.range.c.remainder_bound','pow6.output'),
 ('range3.remainder','range3.slack','crt.range.d.remainder_bound','pow6.output'),
 ('range4.remainder','range4.slack','crt.range.S.remainder_bound','pow11.output'),
 ('range5.remainder','range5.slack','crt.range.Sp.remainder_bound','pow11.output'),
 ('range6.remainder','range6.slack','crt.range.u.remainder_bound','pow14.output'),
 ('range7.remainder','range7.slack','crt.range.vq.remainder_bound','pow14.output'),
 ('range8.remainder','range8.slack','crt.range.index.remainder_bound','pow4.output'),
 ('range9.remainder','range9.slack','crt.range.derived_label_sum.remainder_bound','pow6.output'),
]

def load(path):
    return json.loads(path.read_text())

def pins():
    manifest=load(HERE/'PARENT_PINS.json')
    for name,expected in manifest['files'].items():
        need(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==expected,'parent byte identity: '+name)
    return len(manifest['files'])

def parent_bundle():
    return C.load_bundle(HERE/'parent'/'strict_dimension',HERE/'parent'/'portable_input')

def source_check(parent,data):
    old=parent['guarded']; oldc=parent['transform_certificate']
    c=data['pool_certificate']; source=data['source']
    need(old['domain']==source['domain']=='unrestricted integers','pool domain')
    need(c['parent_guarded_sha256']==P.sha(old),'parent guarded binding')
    need(c['parent_transform_sha256']==P.sha(oldc),'parent certificate binding')
    need(c['new_source_sha256']==P.sha(source),'pool source binding')
    names={v['name']:i for i,v in enumerate(old['variables'])}
    deleted=set(); groups={}
    guards=[g for g in oldc['guards'] if g['kind']=='postsemantic_interval']
    need(len(guards)==11,'parent interval census')
    for rn,sn,label,dn in CASES:
        r,s,L=names[rn],names[sn],names[dn]
        matches=[i for i,row in enumerate(old['residuals']) if row['label']==label]
        need(len(matches)==1,'old interval row unique')
        rowid=matches[0]
        expected=P.add(P.v(L),P.sc(P.v(r),-1),P.sc(P.v(s),-1),P.con(-1))
        need(P.norm(old['residuals'][rowid])==expected,'old interval identity')
        gm=[g for g in guards if g['pair']==[r,s]]
        need(len(gm)==1 and gm[0]['bound_row']==rowid,'guard interval matching')
        g=gm[0]; a,b,cc=g['auxiliary']
        gp=P.add(P.mul(P.v(r),P.v(s)),P.sc(P.mul(P.v(a),P.v(a)),-1),P.sc(P.mul(P.v(b),P.v(b)),-1),P.sc(P.mul(P.v(cc),P.v(cc)),-1),P.sc(P.v(cc),-1))
        need(P.norm(old['residuals'][g['row']])==gp,'old ternary product identity')
        deleted.update((rowid,g['row']))
        groups.setdefault(L,[]).append(r)
    need(c['removed_rows']==sorted(deleted),'exact deleted row inventory')
    need(c['removed_row_values']==[old['residuals'][i] for i in sorted(deleted)],'deleted row bytes')
    # Retain every initial scalar certificate; deletion of one is not allowed.
    need(not any(g['row'] in deleted for g in oldc['guards'] if g['kind']=='front_nonnegative'),'initial bootstrap guard removed')
    expected=copy.deepcopy(old)
    expected['variant']+=':symmetric_residue_pools'
    expected['residuals']=[r for i,r in enumerate(old['residuals']) if i not in deleted]
    merge=c['merge']
    if merge is not None:
        need(merge['method']=='aggregate','selected merger method')
        L0,L,q,Q2=(names[s] for s in ['pow4.output','pow6.output','pow2.output','mul.520'])
        small=groups.pop(L0)
        need(small==[names['choose0.remainder'],names['range8.remainder']],'scaled remainder pair')
        S0=len(expected['variables'])
        need(merge=={'method':'aggregate','small_denominator':L0,'large_denominator':L,'radix':q,'radix_square':Q2,'small_remainders':small,'sum_square':S0,'sum_row':len(expected['residuals'])},'aggregate merger metadata')
        definition=P.add(P.v(Q2),P.sc(P.mul(P.v(q),P.v(q)),-1))
        need(any(P.norm(r)==definition for r in expected['residuals']),'existing q-square wire')
        expected['variables'].append({'name':'residue_pool.small_squares','kind':'gate'})
        sp=P.add(P.v(S0),*[P.sc(P.mul(P.v(r),P.v(r)),-1) for r in small])
        expected['residuals'].append({'label':'residue_pool.small_squares','terms':P.terms(sp)})
    need(len(c['groups'])==len(groups),'new pool census')
    for gi,((L,remainders),g) in enumerate(zip(groups.items(),c['groups'])):
        a,b,cc=range(len(expected['variables']),len(expected['variables'])+3)
        need(g=={'denominator':L,'remainders':remainders,'auxiliary':[a,b,cc],'row':len(expected['residuals'])},'pool metadata')
        expected['variables'] += [{'name':f'residue_pool{gi}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        p=P.add(P.mul(P.v(L),P.v(L)),P.con(-1),*[P.sc(P.mul(P.v(r),P.v(r)),-2) for r in remainders],P.sc(P.mul(P.v(a),P.v(a)),-1),P.sc(P.mul(P.v(b),P.v(b)),-1),P.sc(P.mul(P.v(cc),P.v(cc)),-1),P.sc(P.v(cc),-1))
        if merge is not None and L==merge['large_denominator']:
            p=P.add(p,P.sc(P.mul(P.v(merge['radix_square']),P.v(merge['sum_square'])),-2))
        expected['residuals'].append({'label':f'residue_pool.{gi}','terms':P.terms(p)})
    need(source==expected,'whole source differs from proved residue transformation')
    P.literal(source)
    return {'removed_intervals':11,'pools':len(groups),'scaled_pair':merge is not None}

def bundle(path):
    return {name:load(path/(name+'.json')) for name in ['source','pool_certificate','factored_source','factorization_certificate','projected','projection_certificate','equation','translation_certificate','expanded_polynomial','METRICS']}

def endpoint_check(data):
    for key in ['source','factored_source','projected','equation']:
        need(data[key]['domain']=='unrestricted integers','wrong integer domain: '+key)
    f=P.factorization(data['source'],data['factored_source'],data['factorization_certificate'])
    pr=P.projection(data['factored_source'],data['projected'],data['projection_certificate'])
    tr=P.translation(data['projected'],data['equation'],data['translation_certificate'])
    poly,used=P.literal(data['equation'])
    expanded=data['expanded_polynomial']
    n=len(data['equation']['variables'])
    need(expanded['domain']=='unrestricted integers' and expanded['variables']==n,'expanded domain/census')
    need(P.norm(expanded)==poly,'complete expanded coefficient mismatch')
    need(P.deg(poly)==4,'exact quartic degree')
    need(used==set(range(n)),'non-live input coordinate')
    metrics={'variables':n,'rows':len(data['equation']['residuals']),'degree':4,'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in data['equation']['residuals'] for c,_ in r['terms'])}
    need(all(data['METRICS'][k]==v for k,v in metrics.items()),'exact metric mismatch')
    return metrics|{'factorization_edits':f,'monic_restorations':pr,'integral_translations':tr,'equation_sha256':P.sha(data['equation']),'polynomial_sha256':P.sha(expanded)}

def check_variant(parent,path,centered):
    data=bundle(path)
    result={'source':source_check(parent,data),'uncentered':endpoint_check(data)}
    cdata=copy.deepcopy(data)
    for k in ['equation','translation_certificate','expanded_polynomial','METRICS']:
        cdata[k]=load(centered/(k+'.json'))
    need(load(centered/'projected.json')==data['projected'],'centered projected ancestor')
    need(cdata['translation_certificate']['source_translation_sha256']==P.sha(data['translation_certificate']),'centering initial translation binding')
    result['centered']=endpoint_check(cdata)
    return result,data

def corruptions(parent,data):
    results={}
    def trial(name,edit,stage):
        changed=copy.deepcopy(data);edit(changed)
        try:stage(changed)
        except (ValueError,KeyError,IndexError,TypeError) as exc:
            results[name]={'rejected':True,'reason':str(exc)}
        else:raise ValueError('corruption accepted: '+name)
    def change_pool(d):
        row=next(r for r in d['source']['residuals'] if r['label'].startswith('residue_pool.0'))
        row['terms'].append([1,[]]);d['pool_certificate']['new_source_sha256']=P.sha(d['source'])
    def drop_bootstrap(d):
        rid=parent['transform_certificate']['guards'][0]['row']
        d['pool_certificate']['removed_rows'].append(rid)
        d['pool_certificate']['removed_rows'].sort()
    trial('corrupted_pool_after_rehash',change_pool,lambda d:source_check(parent,d))
    trial('delete_initial_bootstrap_sign',drop_bootstrap,lambda d:source_check(parent,d))
    trial('wrong_denominator_group',lambda d:d['pool_certificate']['groups'][0].__setitem__('denominator',0),lambda d:source_check(parent,d))
    if data['pool_certificate']['merge'] is not None:
        trial('wrong_scaled_remainder',lambda d:d['pool_certificate']['merge']['small_remainders'].__setitem__(0,0),lambda d:source_check(parent,d))
    trial('wrong_factorization_root',lambda d:next(iter(d['factorization_certificate']['square_roots'].values()))[0].__setitem__(0,999),endpoint_check)
    trial('wrong_monic_restoration',lambda d:d['projection_certificate']['steps'][0]['restoration'][0].__setitem__(0,999),endpoint_check)
    trial('wrong_translation',lambda d:d['translation_certificate']['shifts'][0].__setitem__(1,999),endpoint_check)
    trial('wrong_collected_coefficient',lambda d:d['expanded_polynomial']['terms'][0].__setitem__(0,999),endpoint_check)
    trial('wrong_domain',lambda d:d['equation'].__setitem__('domain','nonnegative integers'),endpoint_check)
    trial('wrong_metric',lambda d:d['METRICS'].__setitem__('variables',1),endpoint_check)
    return results

def run(cmd):
    p=subprocess.run([sys.executable,*(['-O'] if sys.flags.optimize else []),'-B',*map(str,cmd)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,cwd=HERE)
    need(p.returncode==0,p.stdout)
    return p.stdout

def rebuild(config):
    result={}
    with tempfile.TemporaryDirectory(prefix='residue_pool_rebuild_') as tmp:
        tmp=Path(tmp)
        for item in config:
            source=HERE/item['source'];centered=HERE/item['centered']
            fresh=tmp/item['source'];final=tmp/item['centered']
            run([HERE/'build.py',HERE/'parent'/'strict_dimension',fresh,'--merge',item['merge'],'--cap',item['cap']])
            run([HERE/'center_integer.py',fresh,final])
            checked=0
            for new,old in [(fresh,source),(final,centered)]:
                newfiles=sorted(p.name for p in new.glob('*.json'))
                oldfiles=sorted(p.name for p in old.glob('*.json'))
                need(newfiles==oldfiles,'rebuild JSON inventory')
                for name in oldfiles:
                    need((new/name).read_bytes()==(old/name).read_bytes(),'rebuild bytes differ: '+str(old/name))
                    checked+=1
            result[item['source']]={'identical_json_files':checked}
    return result

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--receipt',type=Path)
    ap.add_argument('--rebuild',action='store_true')
    args=ap.parse_args()
    pin_count=pins()
    parent=parent_bundle()
    oldmetrics=C.check(parent)
    oldcentered=copy.deepcopy(parent)
    olddir=HERE/'parent'/'strict_dimension_centered'
    need(load(olddir/'projected.json')==parent['projected'],'centered comparison ancestor')
    for name in ['equation','translation_certificate','expanded_polynomial']:
        oldcentered[name]=load(olddir/(name+'.json'))
    oldcentered['METRICS'].update(load(olddir/'METRICS.json'))
    need(oldcentered['translation_certificate']['source_translation_sha256']==P.sha(parent['translation_certificate']),'centered comparison translation binding')
    oldcenteredmetrics=C.check(oldcentered)
    config=load(HERE/'ENDPOINTS.json')['variants']
    results={};controls={}
    for item in config:
        result,data=check_variant(parent,HERE/item['source'],HERE/item['centered'])
        need(all(result['centered'][k]==v for k,v in item['metrics'].items()),'endpoint index metrics')
        need(result['centered']['equation_sha256']==item['equation_sha256'] and result['centered']['polynomial_sha256']==item['polynomial_sha256'],'endpoint index hashes')
        results[item['source']]=result
        controls[item['source']]=corruptions(parent,data)
    out={'status':'passed','optimized':bool(sys.flags.optimize),'scope':'Exact source mutation, old calibration artifact binding, factorization, integral monic restoration, translations, whole quartic coefficients, domains, variable liveness and corruption controls. The mathematical proof is separate.','parent_files_authenticated':pin_count,'parent':{'uncentered':oldmetrics,'centered':oldcenteredmetrics},'variants':results,'corruption_controls':controls}
    if args.rebuild:out['rebuild']=rebuild(config)
    if args.receipt:args.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
