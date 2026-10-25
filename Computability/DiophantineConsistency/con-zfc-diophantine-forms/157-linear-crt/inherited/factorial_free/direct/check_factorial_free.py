#!/usr/bin/env python3
"""Independent exact source, projection, row-basis and quartic checker.

No producing/search module is imported. The old Horn-factoring checker is
retained as a separately authored dependency. This verifies finite algebra,
not the unbounded generalized-CRT or proof-calculus theorems.
"""
from collections import defaultdict
from pathlib import Path
import argparse,copy,hashlib,json,subprocess,sys

ROOT=Path(__file__).resolve().parent
def need(test,message):
    if not test:raise ValueError(message)
def read(p):return json.loads(p.read_text())
def poly(ts):
    p=defaultdict(int)
    for c,m in ts:
        need(isinstance(c,int) and isinstance(m,list),'bad sparse term')
        p[tuple(sorted(m))]+=c
    return {m:c for m,c in p.items() if c}
def plus(*ps):
    p=defaultdict(int)
    for q in ps:
        for m,c in q.items():p[m]+=c
    return {m:c for m,c in p.items() if c}
def scale(p,k):return {m:c*k for m,c in p.items() if c*k}
def times(p,q):
    r=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}
def subst(p,x,q):
    r={}
    for m,c in p.items():
        s={():c}
        for j in m:s=times(s,q if j==x else var(j))
        r=plus(r,s)
    return r
def var(i):return {(i,):1}
def const(c):return {():c} if c else {}
def terms(p):return [[c,list(m)]for m,c in sorted(p.items())]
def degree(p):return max(map(len,p),default=0)
def hsh(p):return hashlib.sha256(p.read_bytes()).hexdigest()

PINS={
 'parent/data/guarded.json':'24ec75ebe002fdc8b2cd0b7e2112fbf254f66fbbb96af44b217c9af3247bdc5a',
 'parent/data/remainder_transformation.json':'95f16a9b1a7a4a3b811d85459ecac03c2f249f24ee154264d047a1056cf1fb39',
 'parent/data/parent_transform_certificate.json':'218e21b1843848a21c90b67b652865f0acfa5e72bafe353a9c5fc018e9db1c76',
 'parent/equation/equation.json':'359a38d9ba49f94e1fff7697ff1af7c5b8a6273d56096f6405fc67f212e8d31d'}

def source_check(folder,new=None):
    old=read(ROOT/'parent/data/guarded.json')
    meta=read(ROOT/'parent/data/remainder_transformation.json')
    cert=read(folder/'mutation.json')
    actual=new if new is not None else read(folder/'raw_source.json')
    square=cert['square_beta'];need(type(square) is bool,'beta profile flag')
    alias=cert.get('alias_majorant',False);need(type(alias)is bool,'majorant alias flag')
    affine_base=cert.get('affine_base',False);need(type(affine_base)is bool and(not affine_base or alias),'affine-base flag')
    names={v['name']:i for i,v in enumerate(old['variables'])}
    t=names['t0'];x=names['x'];y=names['y'];f=names['fact0.output'];r2=names['mul.1'];b=names['choose0.output'];u=names['pow0.output']
    rem=names['fact0.remainder'];slack=names['fact0.slack'];bf=names['mul.5'];q=names['pow2.output'];o=names['choose0.oslack'];A=names['shared.A'];yt=names['index0.Y']
    need(poly(old['residuals'][0]['terms'])==plus(var(r2),scale(times(var(f),var(f)),-1)),'R=F^2 source identity')
    bylabel={}
    for i,row in enumerate(old['residuals']):bylabel.setdefault(row['label'],[]).append(i)
    def one(label):
        need(len(bylabel.get(label,[]))==1,'unique '+label);return bylabel[label][0]
    gr=next(g for g in meta['new_guards'] if g.get('coordinate')==rem)
    gs=next(g for g in meta['new_guards'] if g.get('coordinate')==slack)
    gq=next(g for g in meta['new_guards'] if g.get('coordinate')==o)
    # Bind every deleted semantic relation to its literal intended identity.
    expected_labels={
        'fact0.ceiling':plus(var(b),var(u),const(-1),scale(var(rem),-1),scale(var(bf),-1)),
        'fact0.remainder_bound':plus(var(b),const(-1),scale(var(rem),-1),scale(var(slack),-1)),
        'cofinal.beta_base':plus(var(y),var(u),scale(times(var(u),var(u)),-1)),
        'choose0.digit_bound':plus(var(q),scale(var(b),-1),scale(var(o),-1),const(-1))}
    for label,expected in expected_labels.items():need(poly(old['residuals'][one(label)]['terms'])==expected,'old semantic '+label)
    bfpoly=plus(var(bf),scale(times(var(f),var(b)),-1))
    hits=[i for i,row in enumerate(old['residuals']) if poly(row['terms'])==bfpoly];need(len(hits)==1,'unique BF gate')
    dropped={one(lab) for lab in expected_labels}|{hits[0],gs['row'],gq['row']}
    removed={rem,slack,bf,*gs['auxiliary'],o,*gq['auxiliary']}
    if square:removed.update(gr['auxiliary'])
    for i,row in enumerate(old['residuals']):
        if i not in dropped and i!=gr['row']:need(not any(removed.intersection(m) for _,m in row['terms']),'private-coordinate deletion')
    variables=copy.deepcopy(old['variables'])
    variables[f]['name']='crt.growth_majorant_F';variables[u]['name']='growth.power_U'
    d=len(variables);z=d+1
    variables += [{'name':'growth.power_base','kind':'gate'},{'name':'radix.odd_square_root_half','kind':'signed_witness'}]
    if square:
        sb=len(variables);vb=sb+1
        variables += [{'name':'beta.odd_square_multiplier','kind':'gate'},{'name':'beta.odd_square_root_half','kind':'signed_witness'}]
    oldbase=plus(var(r2),const(1));newbase=var(d)
    updates={}
    # Independently find the base0 multiplying gates by their original
    # polynomials; arithmetic output-wire IDs are not trusted from the edit log.
    pairs=[(scale(times(var(A),oldbase),2),scale(times(var(A),newbase),2)),
        (times(oldbase,oldbase),times(newbase,newbase)),
        (times(oldbase,var(yt)),times(newbase,var(yt)))]
    for before,after in pairs:
        candidates=[]
        for i,row in enumerate(old['residuals']):
            p=poly(row['terms'])
            for m,c in p.items():
                if len(m)==1 and c==1 and plus(p,scale(var(m[0]),-1))==scale(before,-1):candidates.append((i,m[0]))
        need(len(candidates)==1,'unique changed power0 gate');i,v=candidates[0];updates[i]=plus(var(v),scale(after,-1))
    frame=one('shared.frame_definition')
    updates[frame]=plus(poly(old['residuals'][frame]['terms']),times(oldbase,oldbase),scale(times(newbase,newbase),-1))
    hrow=one('self_radix.base_definition');updates[hrow]=plus(poly(old['residuals'][hrow]['terms']),scale(var(b),-1))
    need(poly(old['residuals'][hrow]['terms'])==plus(var(names['self_radix.BH']),scale(times(var(b),plus(const(10),*[var(names['crt.encoded.'+v]) for v in ['a','b','c','d','S','Sp','u','vq']],var(names['crt.encoded_index_minus_one']))),-1)),'old H=1+sum actual representatives')
    if square:updates[gr['row']]=plus(var(y),scale(times(var(f),var(sb)),-1))
    else:
        a,bb,c=gr['auxiliary'];updates[gr['row']]=plus(var(y),scale(var(f),-1),const(-3),scale(times(var(a),var(a)),-1),scale(times(var(bb),var(bb)),-1),scale(times(var(c),plus(var(c),const(1))),-1))
    expected=copy.deepcopy(old);expected['variables']=variables;expected['variant']+=':factorial_free_generalized_crt'
    rows=[]
    for i,row in enumerate(old['residuals']):
        if i in dropped:continue
        rr=copy.deepcopy(row)
        if i in updates:rr['terms']=terms(updates[i])
        if alias:rr['terms']=terms(subst(poly(rr['terms']),u,var(f)))
        if i==gr['row']:rr['label']='bootstrap.beta_base_square_product' if square else 'bootstrap.beta_base_lower_bound'
        rows.append(rr)
    tplus=plus(var(t),const(17))
    base=scale(tplus,2)if affine_base else scale(times(tplus,tplus),2 if alias else 4)
    added=[{'label':'growth.base_definition','terms':terms(plus(var(d),scale(base,-1)))}]
    if not alias:added.append({'label':'growth.majorant_definition','terms':terms(plus(var(f),scale(times(tplus,var(u)),-2)))})
    added.append({'label':'radix.odd_square','terms':terms(plus(var(q),scale(times(plus(scale(var(z),2),const(1)),plus(scale(var(z),2),const(1))),-1)))})
    if square:added.append({'label':'beta.odd_square_multiplier','terms':terms(plus(var(sb),scale(times(plus(scale(var(vb),2),const(1)),plus(scale(var(vb),2),const(1))),-1)))})
    expected['residuals']=rows+added
    need(expected==actual,'complete factorial-free source reconstruction')
    need(all(degree(poly(r['terms']))<=2 for r in actual['residuals']),'quadratic source')
    need(cert['removed_rows']==sorted(dropped),'deleted row ledger')
    need(cert['removed_private_variables']==sorted(removed),'deleted private ledger')
    need(cert['added_rows']==added,'added row ledger')
    need(cert['source_sha256']==PINS['parent/data/guarded.json'],'source pin')
    need(cert['amplifier_constant']==2,'amplifier parameter')
    if alias:
        need(cert['majorant_alias']==[[u,f]],'majorant coordinate alias')
        need(not any(u in m for row in actual['residuals']for _,m in row['terms']),'old U coordinate absent')
    return actual

def projection_check(folder,source):
    sys.path.insert(0,str(ROOT/'parent/code'))
    import inherited_independent_algebra as IA
    fac=read(folder/'factored_source.json')
    nf=IA.factorization(source,fac,read(folder/'factorization_certificate.json'))
    cert=read(folder/'projection_certificate.json')
    rows={i:poly(r['terms']) for i,r in enumerate(fac['residuals'])};deleted=set()
    for st in cert['steps']:
        i,v=st['row_id'],st['variable'];replacement=poly(st['restoration'])
        need(i in rows and v not in deleted,'valid monic target')
        need(all(v not in m for m in replacement),'acyclic monic target')
        relation=plus(var(v),scale(replacement,-1))
        need(rows[i] in (relation,scale(relation,-1)),'exact unit monic relation')
        del rows[i]
        nextrows={}
        for j,p in rows.items():
            r=subst(p,v,replacement);need(degree(r)<=2,'projected quadratic degree')
            if r:nextrows[j]=r
        rows=nextrows;deleted.add(v)
    keep=cert['retained_original_variables'];used=sorted({v for p in rows.values() for m in p for v in m})
    need(keep==used,'projection liveness')
    need(sorted(rows)==cert['retained_original_rows'],'retained rows')
    unused=sorted(set(range(len(fac['variables'])))-set(keep)-deleted)
    need(unused==cert['unconstrained_removed'],'unconstrained metadata')
    ren={v:i for i,v in enumerate(keep)};pr=read(folder/'projected.json')
    need(pr['variables']==[fac['variables'][i]for i in keep],'projected variable names')
    need(len(pr['residuals'])==len(rows),'projection row count')
    for oi,r in zip(sorted(rows),pr['residuals']):need(poly(r['terms'])=={tuple(ren[v] for v in m):c for m,c in rows[oi].items()},'complete monic output')
    eq=read(folder/'equation.json');tr=read(folder/'translation_certificate.json')
    need(tr['convention']=='old=new+shift','translation convention')
    need(eq['variables']==pr['variables'],'translation variables')
    for oldrow,newrow in zip(pr['residuals'],eq['residuals']):
        p=poly(oldrow['terms'])
        for v,d in tr['shifts']:p=subst(p,v,plus(var(v),const(d)))
        need(p==poly(newrow['terms']),'complete integral translation')
    return {'horn_edits':nf,'monic_projections':len(deleted),'unused_removed':len(unused)}

def quartic_check(folder,equation=None,expanded=None):
    eq=equation if equation is not None else read(folder/'equation.json')
    ep=expanded if expanded is not None else read(folder/'expanded_polynomial.json')
    need(eq['domain']=='unrestricted integers','integer domain')
    total={}
    for row in eq['residuals']:
        p=poly(row['terms']);need(degree(p)<=2,'quadratic residual');total=plus(total,times(p,p))
    need(total==poly(ep['terms']),'complete quartic collection')
    used={i for m in total for i in m};need(used==set(range(len(eq['variables']))),'all coordinates live')
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':degree(total),'monomials':len(total),'height':max(map(abs,total.values())),
        'row_height':max(abs(c)for row in eq['residuals']for c,_ in row['terms'])}
    need(read(folder/'METRICS.json')==metrics,'all exact metrics')
    return metrics

def affine_check(source,folder,cert_override=None):
    cert=cert_override if cert_override is not None else read(folder/'certificate.json')
    names={v['name']:i for i,v in enumerate(source['variables'])}
    rows=[poly(r['terms'])for r in source['residuals']]
    for target,inputs in cert['coordinate_shears']:
        t=names[target];need(target not in inputs,'invertible coordinate shear')
        replacement=plus(var(t),*[{(names[n],):c}for n,c in inputs.items()])
        rows=[subst(p,t,replacement)for p in rows]
    for i,j,k in cert['row_operations']:
        need(i!=j and type(k)is int,'unimodular row shear');rows[i]=plus(rows[i],scale(rows[j],k))
    drop_rows=set();drop_vars=set()
    for st in cert['projections']:
        i,v=st['row'],st['variable'];r=poly(st['replacement'])
        need(degree(rows[i])<=1 and rows[i].get((v,)) in(-1,1),'unit affine elimination')
        need(all(v not in m for m in r),'affine restoration independent')
        need(not subst(rows[i],v,r),'deleted affine row vanishes')
        rows=[subst(p,v,r)for p in rows];drop_rows.add(i);drop_vars.add(v)
    keep=[i for i in range(len(source['variables']))if i not in drop_vars];ren={v:i for i,v in enumerate(keep)}
    rows=[{tuple(ren[x]for x in m):c for m,c in p.items()}for i,p in enumerate(rows)if i not in drop_rows]
    for i,j,k in cert['final_row_operations']:
        need(i!=j and type(k)is int,'final invertible row shear');rows[i]=plus(rows[i],scale(rows[j],k))
    eq=read(folder/'equation.json')
    need(eq['variables']==[source['variables'][i]for i in keep],'affine final variable list')
    need([poly(r['terms'])for r in eq['residuals']]==rows,'complete affine/row-basis endpoint')
    return {'coordinate_shears':len(cert['coordinate_shears']),'affine_exposure_operations':len(cert['row_operations']),
        'unit_affine_projections':len(cert['projections']),'final_row_operations':len(cert['final_row_operations'])}

def negative_controls(source_folder,endpoint):
    results=[]
    def rejects(name,run):
        try:run()
        except (ValueError,KeyError,IndexError):results.append(name);return
        raise ValueError('corruption accepted: '+name)
    raw=read(source_folder/'raw_source.json')
    labels=['radix.odd_square','growth.base_definition','self_radix.base_definition','shared.frame_definition']
    labels+=['growth.majorant_definition']if any(r['label']=='growth.majorant_definition'for r in raw['residuals'])else['beta.odd_square_multiplier']
    for label in labels:
        bad=copy.deepcopy(raw);row=next(r for r in bad['residuals']if r['label']==label);row['terms'][0][0]+=1
        rejects(label,lambda b=bad:source_check(source_folder,b))
    ec=read(endpoint/'certificate.json');bad=copy.deepcopy(ec);bad['projections'][0]['replacement'][0][0]+=1
    rejects('monic inverse coefficient',lambda:affine_check(read(source_folder/'equation.json'),endpoint,bad))
    ep=read(endpoint/'expanded_polynomial.json');badp=copy.deepcopy(ep);badp['terms'][0][0]+=1
    rejects('quartic coefficient',lambda:quartic_check(endpoint,expanded=badp))
    return results

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--receipt',type=Path);p.add_argument('--skip-parent',action='store_true');p.add_argument('--square-beta-only',action='store_true');p.add_argument('--final-only',action='store_true');p.add_argument('--affine-only',action='store_true')
    a=p.parse_args()
    for n,d in PINS.items():need(hsh(ROOT/n)==d,'pinned input '+n)
    parent=None
    if not a.skip_parent:
        r=subprocess.run([sys.executable,'-B',str(ROOT/'parent/code/check.py')],check=True,capture_output=True,text=True)
        parent=json.loads(r.stdout)
    reports={}
    branches=['factorial_free_affine']if a.affine_only else ['factorial_free_final']if a.final_only else ['factorial_free_squarebeta'] if a.square_beta_only else ['factorial_free','factorial_free_squarebeta']
    for name in branches:
        folder=ROOT/name;raw=source_check(folder);replay=projection_check(folder,raw);met=quartic_check(folder)
        items={}
        counts=[242,241]if name.endswith('affine')else[243,242]if name.endswith('final')else[244,243]if name.endswith('squarebeta')else[245,244]
        for count in counts:
            ep=ROOT/(name+str(count)+'_balanced');items[ep.name]={'finite_maps':affine_check(read(folder/'equation.json'),ep),'metrics':quartic_check(ep)}
        negative=negative_controls(folder,ROOT/(name+str(counts[0])+'_balanced'))
        reports[name]={'source_reconstruction':'PASS','projection':replay,'source_endpoint_metrics':met,'endpoints':items,'rejected_corruptions':negative}
    result={'status':'PASS','scope':'Exact finite source, Horn edits, integral monic projections, all coordinate and row transformations, every quartic coefficient; unbounded semantic theorem is separate.','parent':parent,'profiles':reports}
    if a.receipt:a.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
