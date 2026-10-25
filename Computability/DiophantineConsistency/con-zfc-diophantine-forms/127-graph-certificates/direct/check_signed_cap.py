#!/usr/bin/env python3
"""Independent source/sign/whole-polynomial verification for signed caps.

No source constructor, sign inference producer, or coordinate optimizer is
imported. The unbounded number theory remains in SIGNED_CAP_PROOF.md.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter
from hashlib import sha256
import argparse,json
import check_capped_modular as C
from check_affine_export import verify as affine_verify

HERE=Path(__file__).resolve().parent
need=C.need

def load(path):return json.loads(path.read_text())
def canonical(obj):return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()
def polynomial(terms):return C.add(*({tuple(m):c} for c,m in terms))
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def neg(p):return C.scale(-1,p)
def substitute(p,v,f):
    return C.add(*(C.scale(c,C.mul(*(f if i==v else C.var(i) for i in m))) for m,c in p.items()))

def source_check(meta,raw,source,cert):
    receipt,affine=affine_verify(meta,raw)
    old_ids=affine['retained_original_indices_in_target_order']
    rename={v:i for i,v in enumerate(old_ids)}
    exp=C.Expander(meta,set(old_ids))
    def atom(a):
        p=C.atom(a) if a[0]=='c' else exp.variable(a[1])
        need(all(v in rename for m in p for v in m),'unmapped semantic coordinate')
        p={tuple(rename[v] for v in m):c for m,c in p.items()}
        need(all(len(m)<=1 for m in p),'semantic port not affine')
        return p
    frame=sorted({tuple(p[k]) for p in meta['powers'] for k in ('base','exponent','output')}|
                 {tuple(p['n']) for p in meta['modular_requests']})
    W,A=map(atom,meta['scale'][:2]);cc=meta['cap_certificate']
    yc=atom(cc['cap']['pair'][1]);slack=atom(cc['aggregate']['slack'])
    seed=[(atom(s['exponent']),atom(s['pair'][0]),atom(s['pair'][1])) for s in meta['seeds']]
    changes={
        'shared.frame_definition':C.sub(W,C.add(C.const(2),*(C.square(atom(a)) for a in frame))),
        'index_cap.all_indices_bound':C.sub(yc,C.add(W,C.const(1),slack,*(C.square(y) for k,x,y in seed))),
        'index_cap.squared_index_errors':C.sub(C.add(*(C.add(C.square(C.sub(y,k)),C.square(C.sub(x,C.const(1))))
            for k,x,y in seed)),C.mul(C.sub(A,C.const(1)),atom(cc['residue']['quotient'])))}
    expected=deepcopy(raw);expected.pop('metrics',None)
    expected['domain']='unrestricted integers';expected['variant']+=':oriented_signed_cap'
    recorded=[]
    for label,p in changes.items():
        hits=[i for i,r in enumerate(expected['residuals']) if r['label']==label]
        need(len(hits)==1,'nonunique changed row')
        i=hits[0];old=deepcopy(expected['residuals'][i])
        expected['residuals'][i]['terms']=terms(p)
        recorded.append({'row':i,'old':old,'new':expected['residuals'][i]})
    need(source==expected,'mixed source differs from the three exact source changes')
    need(cert['changes']==recorded,'wrong changed-row certificate')
    need(cert['frame_atoms']==[{'token':list(a),'affine':terms(atom(a))} for a in frame],
         'wrong square frame certificate')
    need(cert['seeds']==[{'exponent':terms(k),'X':terms(x),'Y':terms(y)} for k,x,y in seed],
         'wrong signed seed certificate')
    # Each exponent occurs as a distinct square-frame atom. Its positivity
    # uses only earlier source witnesses, never a principal pair or quotient.
    need({tuple(s['exponent']) for s in meta['seeds']}<=set(frame),'uncapped exponent')
    need(len(seed)==15 and len({tuple(s['exponent']) for s in meta['seeds']})==15,
         'wrong distinct positive index count')
    return {'three_changed_rows_exact':True,'all_other_source_rows_unchanged':True,
            'semantic_frame_atoms':len(frame),'signed_pell_pairs':len(seed),
            'affine_raw_binding':receipt}

def expected_exempt(meta,source,late):
    names={v['name']:i for i,v in enumerate(source['variables'])}
    n={meta['variables'][a[1]]['name'] for s in meta['seeds'] for a in s['pair']}
    n|={meta['variables'][r['quotient'][1]]['name'] for r in meta['modular_requests']}
    n|={'pow'+str(i)+'.quotient' for i in range(len(meta['powers']))}
    n.add('index_cap.error_square_quotient')
    if late:
        n|={meta['variables'][p['output'][1]]['name'] for p in meta['powers']}
        n|={'base'+str(i)+'.T' for i in range(len({tuple(p['base']) for p in meta['powers']}))}
        n|={'modular.root_quotient','crt.index_quotient','crt.nonnegative_quotient'}
    need(n<=set(names),'exempt semantic coordinate is absent')
    return {names[s] for s in n},n

def sign_check(meta,source,guarded,cert,late):
    exempt,names=expected_exempt(meta,source,late)
    need(cert['exempt_names']==sorted(names),'wrong exempt roles')
    need(cert['semantic_signed']==sorted(exempt),'wrong exempt indices')
    required={i for i,v in enumerate(source['variables']) if v['kind'] not in ('gate','square_difference')}-exempt
    need(cert['semantic_required']==sorted(required),'wrong required nonnegative coordinates')
    guards=cert['guard_indices']
    need(guards==sorted(set(guards)) and set(guards)<=required,'invalid guard index list')
    expected=deepcopy(source)
    for v in guards:
        a,b,c=range(len(expected['variables']),len(expected['variables'])+3)
        expected['variables'] += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        expected['residuals'].append({'label':f'nonnegative.{v}','terms':terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    need(guarded==expected,'guard graph is not exactly the stated nonnegative representation')
    known=set(guards)
    for step in cert['proof_steps']:
        v=step['variable'];need(v not in known,'duplicate sign derivation')
        p=polynomial(source['residuals'][step['row']]['terms'])
        c=p.get((v,),0);need(c!=0 and abs(c)==step['coefficient'],'wrong sign derivation coefficient')
        rhs={m:-a*(1 if c>0 else -1) for m,a in p.items() if m!=(v,)}
        need(all(v not in m for m in rhs),'self-referential sign derivation')
        need(terms(rhs)==step['rhs'],'sign proof did not reproduce the actual row')
        if step['kind']=='positive_monomials':
            need(all(a>0 for a in rhs.values()),'negative monomial in sign proof')
            deps={i for m in rhs for i,e in Counter(m).items() if e%2}
            need(deps<=known and sorted(deps)==step['dependencies'],'unknown odd sign dependency')
        elif step['kind']=='affine_square':
            root=polynomial(step['square_root'])
            need(all(len(m)<=1 for m in root) and C.square(root)==rhs,'invalid square sign witness')
            need(step['dependencies']==[],'square sign witness has extraneous dependencies')
        else:raise ValueError('unknown sign rule')
        known.add(v)
    need(required<=known,'required semantic sign has no finite proof')
    need(cert['known_nonnegative']==sorted(known),'wrong final sign closure')
    cap_names={'index_cap.'+s for s in ('X','Y','U','V','S','R','q4minus1',
               'Vquotient_minus1','Bquotient','Squotient','Rquotient','aggregate_slack')}
    source_names={v['name']:i for i,v in enumerate(source['variables'])}
    need({source_names[n] for n in cap_names}<=known,'one indexed cap lacks natural witnesses')
    preframe=meta['scale'][0][1]
    prefix_witness_names={v['name'] for v in meta['variables'][:preframe] if v['kind'] not in ('gate','square_difference')}
    late_output_names={meta['variables'][p['output'][1]]['name'] for p in meta['powers']} if late else set()
    need({source_names[n] for n in prefix_witness_names if n in source_names and n not in names}<=known,
         'presemantic source witness is not natural')
    # Re-establish the exact pre-power positivity cut over the mixed domain.
    # No nonnegative lower bound is assigned to an exempt power output.
    defs={r['gate']:r for r in meta['rows'] if r['gate'] is not None};memo={}
    def lower(a):
        if a[0]=='c':return min(2,a[1])
        i=a[1]
        if i in memo:return memo[i]
        if i not in defs:
            name=meta['variables'][i]['name']
            need(name in source_names and source_names[name] in known,
                 'positive index depends on an unproved semantic sign: '+name)
            return 0
        p=polynomial(defs[i]['terms'])
        need(p.get((i,))==1,'positive-index gate is not monic')
        rhs={m:-c for m,c in p.items() if m!=(i,)}
        need(all(c>=0 and all(j<i for j in m) for m,c in rhs.items()),
             'index positivity used a nonmonotone or cyclic gate')
        total=0
        for m,c in rhs.items():
            value=min(2,c)
            for j in m:value=min(2,value*lower(['v',j]))
            total=min(2,total+value)
        memo[i]=total;return total
    positive=[lower(s['exponent']) for s in meta['seeds']]
    need(all(b>=1 for b in positive),'one signed-cap index is not positive before powers')
    powers=meta['powers']
    need(len(powers)==6 and powers[2]['base']==powers[1]['output'] and
         all(p['base']==powers[2]['output'] for p in powers[3:]),
         'wrong sequential positive-base power schedule')
    need(lower(powers[0]['base'])>=1 and lower(powers[1]['base'])>=2,
         'the first two power bases are not independently positive')
    return {'guards':len(guards),'sign_steps':len(cert['proof_steps']),
            'all_required_semantic_signs_proved':True,'exempt_semantic_coordinates':len(exempt),
            'cap_natural_witnesses_proved_before_index_semantics':True,
            'positive_indices_before_powers':len(positive),
            'sequential_positive_base_schedule_verified':True}

def projection_check(source,target,certificate,full):
    need(certificate['schema']=='integer_quadratic_elimination_v1','wrong signed projection schema')
    need(sha256(canonical(source)).hexdigest()==certificate['input_sha256'],'projection source hash')
    need(sha256(canonical(target)).hexdigest()==certificate['output_sha256'],'projection target hash')
    rows={i:polynomial(r['terms']) for i,r in enumerate(source['residuals'])};deleted=set()
    for step in certificate['steps']:
        rid,v=step['row_id'],step['variable'];f=polynomial(step['restoration'])
        need(rid in rows and v not in deleted,'invalid projection step')
        need(all(v not in m and len(m)<=2 for m in f),'invalid integer restoration')
        expected=C.sub(C.var(v),f)
        need(rows[rid] in (expected,neg(expected)),'deleted row is not the claimed monic equation')
        new={}
        for j,p in rows.items():
            if j==rid:continue
            q=substitute(p,v,f)
            need(all(len(m)<=2 for m in q),'projection raises residual degree')
            if q:new[j]=q
        rows=new;deleted.add(v)
    ordered=sorted({v for p in rows.values() for m in p for v in m})
    need(certificate['retained_original_variables']==ordered,'wrong retained variable order')
    need(certificate['retained_original_rows']==sorted(rows),'wrong retained row order')
    unused=sorted(set(range(len(source['variables'])))-deleted-set(ordered))
    need(certificate['unconstrained_removed']==unused==[],'unconstrained coordinate removed')
    remap={v:i for i,v in enumerate(ordered)}
    expected=[{'label':source['residuals'][j]['label'],
        'terms':terms({tuple(remap[v] for v in m):c for m,c in p.items()})} for j,p in sorted(rows.items())]
    need(target['residuals']==expected,'projected polynomial rows differ')
    need(target['variables']==[source['variables'][v] for v in ordered],'projected variable descriptions differ')
    whole=C.add(*(C.square(polynomial(r['terms'])) for r in target['residuals']))
    need(full['domain']=='unrestricted integers' and full['variables']==len(ordered),
         'wrong whole polynomial domain or variable count')
    need(full['terms']==terms(whole),'whole quartic coefficient list differs')
    return {'variables':len(ordered),'rows':len(rows),'restorations':len(deleted),
            'degree':max(map(len,whole)),'monomials':len(whole),
            'coefficient_height':max(map(abs,whole.values())),'unconstrained_removed':0}

def run(directory,corruptions=True):
    directory=Path(directory)
    meta=load(HERE/'equation240/raw/raw_audit_input.json');raw=load(HERE/'equation240/raw/equation.json')
    source=load(directory/'mixed_source.json');sourcecert=load(directory/'source_certificate.json')
    guarded=load(directory/'guarded.json');signcert=load(directory/'sign_certificate.json')
    target=load(directory/'equation.json');proj=load(directory/'projection_certificate.json')
    full=load(directory/'expanded_polynomial.json');metrics=load(directory/'METRICS.json')
    a=source_check(meta,raw,source,sourcecert)
    b=sign_check(meta,source,guarded,signcert,metrics.get('late_signs',False))
    c=projection_check(guarded,target,proj,full)
    need((c['variables'],c['rows'],c['monomials'],c['coefficient_height'])==
         (metrics['output_variables'],metrics['output_rows'],metrics['expanded_monomials'],metrics['max_abs_expanded_coefficient']),
         'integer endpoint metrics do not match literal coefficients')
    rejects=[]
    if corruptions:
        def reject(title,fun):
            try:fun()
            except ValueError:rejects.append(title)
            else:raise ValueError('corruption accepted: '+title)
        bad=deepcopy(source);bad['residuals'][sourcecert['changes'][0]['row']]['terms'][0][0]+=1
        reject('square frame coefficient',lambda:source_check(meta,raw,bad,sourcecert))
        bad=deepcopy(guarded);bad['residuals'][-1]['terms'][0][0]+=1
        reject('nonnegative guard coefficient',lambda:sign_check(meta,source,bad,signcert,metrics.get('late_signs',False)))
        bad=deepcopy(signcert);bad['proof_steps'][0]['coefficient']+=1
        reject('sign proof coefficient',lambda:sign_check(meta,source,guarded,bad,metrics.get('late_signs',False)))
        bad=deepcopy(proj);bad['steps'][0]['restoration'][0][0]+=1
        reject('integer restoration coefficient',lambda:projection_check(guarded,target,bad,full))
        bad=deepcopy(full);bad['terms'][0][0]+=1
        reject('collected quartic coefficient',lambda:projection_check(guarded,target,proj,bad))
    return {'status':'PASS','source':a,'signs':b,'endpoint':c,'corruptions_rejected':rejects,
        'producer_or_optimizer_imported':False,
        'scope':'Exact finite source, sign, projection and quartic coefficient checks; ordinary signed-cap proof is separate.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    result=run(a.directory);body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(body)
    print(body,end='')
