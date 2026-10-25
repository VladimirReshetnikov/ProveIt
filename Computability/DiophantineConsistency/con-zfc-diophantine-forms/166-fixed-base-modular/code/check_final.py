#!/usr/bin/env python3
"""Independent finite audit of the compressed frame, cofinal center and endpoints.

No producer, factorizer, projection optimizer, or source compiler is imported.
"""
import argparse,copy,hashlib,importlib.util,json
from collections import defaultdict
from pathlib import Path
from independent_polynomials import need,norm,mul,sub,canon

HERE=Path(__file__).resolve().parent
PACKAGED=(HERE.parent/'stages').is_dir()
FIXED=HERE.parent/'stages/fixed_base' if PACKAGED else HERE.parent/'alternative_encoding/fixed_base16_linear_B'
MODULAR=HERE.parent/'stages/modular' if PACKAGED else HERE.parent/'literature_audit/modular'
COMPRESSED=HERE.parent/'stages/compressed' if PACKAGED else HERE/'frame_compressed'
BALANCED=HERE.parent/'equations/balanced' if PACKAGED else HERE/'final230'
COMPACT=HERE.parent/'equations/compact' if PACKAGED else HERE/'final229'
PARENT=(HERE.parent/'upstream/factorial_free/direct' if PACKAGED else HERE.parents[1]/'sources/incoming/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct')
def read(p):return json.loads(p.read_text())
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(p,k):return {m:k*c for m,c in p.items() if k*c}
def var(v):return {(v,):1}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]

def source_delta():
    old=read(MODULAR/'raw_source.json')
    new=read(COMPRESSED/'raw_source.json')
    cert=read(COMPRESSED/'mutation.json')
    need(hashlib.sha256(canon(old)).hexdigest()==cert['source_sha256'],'modular source identity')
    n={v['name']:i for i,v in enumerate(old['variables'])}
    t=add(var(n['t0']),{():16});q=var(n['pow2.output']);R=var(n['radius.R'])
    atoms=[{():16},add(t,{():1}),add(q,{():1}),R,var(n['pow6.output'])]
    fi=next(i for i,r in enumerate(old['residuals']) if r['label']=='shared.frame_definition')
    ci=next(i for i,r in enumerate(old['residuals']) if r['label']=='free_A.cofinal_constructor')
    expected=copy.deepcopy(old)
    expected['residuals'][fi]['terms']=terms(add(norm(old['residuals'][fi]['terms']),*[mul(p,p) for p in atoms]))
    A,L,u,v=[n[s] for s in ['shared.A','frame.L','free_A.u','free_A.v']]
    expected['residuals'][ci]['terms']=terms({(A,):1,(L,L):-1,(u,u):-1,(v,v):-1})
    expected['variant']='common_modular_numerators_affine_frame_two_square_center'
    need(expected==new,'only five frame atoms and two-square center changed')
    need([terms(a) for a in atoms]==cert['removed_square_atoms'],'exact removed atom list')
    need(cert['row']==fi and cert['center_change']['row']==ci,'mutation row binding')
    need(cert['old_row']==old['residuals'][fi] and cert['new_row']==new['residuals'][fi],'frame delta binding')
    need(cert['center_change']['old_row']==old['residuals'][ci] and cert['center_change']['new_row']==new['residuals'][ci],'center delta binding')
    # Full exact-power / modular-index frame audit: derive it from the retained
    # first mutation's literal eighteen requests, then account for each deletion.
    req=read(FIXED/'mutation.json')['requests']
    frame_atoms={tuple(sorted(norm(p).items())):norm(p) for r in req for p in [r['base'],r['exponent'],r['output']]}
    modular=[3,5,7,8,9,10,12,13,15,16,17]
    for j in modular:
        p=norm(req[j]['output']);need(tuple(sorted(p.items())) in frame_atoms,'modular output existed')
        del frame_atoms[tuple(sorted(p.items()))]
    for p in atoms:
        key=tuple(sorted(p.items()));need(key in frame_atoms,'removed atom existed once');del frame_atoms[key]
    expected_frame=add(var(n['shared.W']),{():-2},*[scale(mul(a,a),-1) for a in frame_atoms.values()])
    need(expected_frame==norm(new['residuals'][fi]['terms']),'entire 21-atom frame')
    for p in [t,add(R,t),q]:need(tuple(sorted(p.items())) in frame_atoms,'strict-bound anchor retained')
    horizon=n['cofinal.horizon_root']
    need(any(r['label']=='cofinal.horizon' and norm(r['terms'])=={(n['t0'],):1,(horizon,horizon):-1} for r in new['residuals']),'t=16+h²')
    used={i for r in new['residuals'] for _,m in r['terms'] for i in m}
    need(n['free_A.w'] not in used,'third center witness unused after source change')
    return {'raw_rows':len(new['residuals']),'retained_frame_atoms':len(frame_atoms),
        'removed_frame_atoms':5,'center_witnesses':2,
        'strict_bound_certificate':'t>=16; W>=t²+2>=258; R²<=2((R+t)²+t²)<=2(W-2)<W²; q²+2>|q+1|',
        'successor_output':'retained exact multiplication q*D_t, with no frame bound needed',
        'raw_sha256':hashlib.sha256(canon(new)).hexdigest()}

def factorization(corrupt=False):
    # This retained checker imports only standard-library modules; it does not
    # import the producer, its factorizer, or the projection optimizer.
    path=PARENT/'parent/code/inherited_independent_algebra.py'
    spec=importlib.util.spec_from_file_location('retained_independent_auditor',path)
    auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
    source=read(COMPRESSED/'raw_source.json');target=read(COMPRESSED/'factored_source.json');certificate=read(COMPRESSED/'factorization_certificate.json')
    if corrupt:next(iter(certificate['square_roots'].values()))[0][0]+=1
    return {'independent_exact_edits':auditor.factorization(source,target,certificate),
        'auditor_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def projection_and_translation():
    folder=COMPRESSED;src=read(folder/'factored_source.json');pr=read(folder/'projected.json');cert=read(folder/'projection_certificate.json')
    need(hashlib.sha256(canon(src)).hexdigest()==cert['input_sha256'],'projection source hash')
    need(hashlib.sha256(canon(pr)).hexdigest()==cert['output_sha256'],'projection result hash')
    rows={i:norm(r['terms']) for i,r in enumerate(src['residuals'])};dead=set()
    for s in cert['steps']:
        i=s['row_id'];v=s['variable'];p=norm(s['restoration']);need(v not in dead,'coordinate deleted once')
        need(v not in {w for m in p for w in m},'acyclic monic restoration')
        target=add(var(v),scale(p,-1));need(rows[i] in [target,scale(target,-1)],'actual monic row')
        rows={j:sub(r,v,p) for j,r in rows.items() if j!=i}
        rows={j:r for j,r in rows.items() if r}
        need(all(len(m)<=2 for r in rows.values() for m in r),'quadratic row degree')
        dead.add(v)
    keep=cert['retained_original_variables'];ren={v:i for i,v in enumerate(keep)}
    used={v for r in rows.values() for m in r for v in m}
    need(keep==sorted(used),'retained variable set')
    need(cert['unconstrained_removed']==sorted(set(range(len(src['variables'])))-dead-used),'unused coordinates')
    literal=[{'label':src['residuals'][i]['label'],'terms':[[c,[ren[v] for v in m]] for m,c in sorted(r.items())]} for i,r in sorted(rows.items())]
    need(literal==pr['residuals'],'all projected rows')
    need([src['variables'][v] for v in keep]==pr['variables'],'projected variable names')
    tc=read(folder/'translation_certificate.json');eq=read(folder/'equation.json')
    translated=[norm(r['terms']) for r in pr['residuals']]
    for v,k in tc['shifts']:translated=[sub(r,v,add(var(v),{():k})) for r in translated]
    need([terms(r) for r in translated]==[r['terms'] for r in eq['residuals']],'all coordinate translations')
    return {'monic_restorations':len(dead),'unused_removed':len(cert['unconstrained_removed']),
        'projected_variables':len(keep),'projected_rows':len(literal),'translations':len(tc['shifts'])}

def endpoint(name,corrupt=None):
    folder={'balanced':BALANCED,'compact':COMPACT}[name];src=read(COMPRESSED/'equation.json');eq=read(folder/'equation.json');cert=read(folder/'certificate.json')
    need(hashlib.sha256(canon(src)).hexdigest()==cert['input_sha256'],'refinement input identity')
    need(hashlib.sha256(canon(eq)).hexdigest()==cert['output_sha256'],'refinement result identity')
    rows=[norm(r['terms']) for r in src['residuals']];dead=set();deleted=set()
    if corrupt=='projection':
        next(x for x in cert['operations'] if x['type']=='projection')['restoration'][0][0]+=1
    if corrupt=='row_operation':
        next(x for x in cert['operations'] if x['type']=='row_add')['multiple']+=1
    for s in cert['operations']:
        typ=s['type']
        if typ=='translation':
            v=s['variable'];p=add(var(v),{():s['delta']});rows=[sub(r,v,p) for r in rows]
        elif typ=='shear':
            v=s['variable'];p=norm(s['restoration'])
            need(p.get((v,))==1 and all(len(m)<=1 for m in p),'unit triangular affine shear')
            need(sum(v in m for m in p)==1,'shear has no other target occurrences')
            rows=[sub(r,v,p) for r in rows]
        elif typ=='row_add':
            i,j,k=s['target'],s['source'],s['multiple'];need(i!=j,'invertible row addition')
            need(i not in deleted and j not in deleted,'live row operation')
            rows[i]=add(rows[i],scale(rows[j],k))
        elif typ=='projection':
            i=s['row'];v=s['variable'];p=norm(s['restoration'])
            need(v not in {w for m in p for w in m} and all(len(m)<=1 for m in p),'acyclic affine projection')
            target=add(var(v),scale(p,-1));need(rows[i] in [target,scale(target,-1)],'actual affine consequence')
            rows=[sub(r,v,p) for r in rows];need(not rows[i],'deleted row zero')
            dead.add(v);deleted.add(i)
        else:raise ValueError('unknown certificate operation')
    keep=cert['retained_variables'];rr=cert['retained_rows'];ren={v:i for i,v in enumerate(keep)}
    need(keep==[i for i in range(len(src['variables'])) if i not in dead],'complete variable map')
    need(rr==[i for i in range(len(rows)) if i not in deleted],'complete row map')
    literal=[{'label':src['residuals'][i]['label'],'terms':[[c,[ren[v] for v in m]] for m,c in sorted(rows[i].items())]} for i in rr]
    need(literal==eq['residuals'],'every final residual')
    need([src['variables'][v] for v in keep]==eq['variables'],'every final variable')
    pol=defaultdict(int)
    for r in literal:
        p=norm(r['terms']);need(all(len(m)<=2 for m in p),'final quadratic degree')
        for m,c in mul(p,p).items():pol[m]+=c
    pol={m:c for m,c in pol.items() if c};stored=read(folder/'expanded_polynomial.json')
    if corrupt=='coefficient':stored['terms'][0][0]+=1
    need(pol==norm(stored['terms']),'all quartic coefficients')
    need({v for m in pol for v in m}==set(range(len(keep))),'all coordinates occur')
    met={'variables':len(keep),'rows':len(rr),'degree':max(map(len,pol)),'monomials':len(pol),
        'height':max(map(abs,pol.values())),'row_height':max(abs(c) for r in literal for c,m in r['terms'])}
    need(met==read(folder/'METRICS.json'),'all measured metrics')
    return {'metrics':met,'operations':len(cert['operations']),'affine_projections':len(dead),'equation_sha256':hashlib.sha256(canon(eq)).hexdigest()}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    for name,default in [('fixed-base',FIXED),('modular',MODULAR),('compressed',COMPRESSED),('balanced',BALANCED),('compact',COMPACT),('parent',PARENT)]:ap.add_argument('--'+name,type=Path,default=default)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args();FIXED=a.fixed_base;MODULAR=a.modular;COMPRESSED=a.compressed;BALANCED=a.balanced;COMPACT=a.compact;PARENT=a.parent
    report={'source_delta':source_delta(),'horn_factorization':factorization(),'projection_translation':projection_and_translation(),
        'balanced':endpoint('balanced'),'compact':endpoint('compact')}
    controls=0
    for name in ['balanced','compact']:
        for corruption in ['projection','row_operation','coefficient']:
            try:endpoint(name,corruption)
            except ValueError:controls+=1
            else:raise ValueError('corruption accepted')
    try:factorization(True)
    except ValueError:controls+=1
    else:raise ValueError('corrupt Horn factor accepted')
    report.update(status='PASS',corruption_controls_rejected=controls,
        scope='Exact source delta, independently checked Horn factoring, all monic/affine transformations and every collected coefficient. The unbounded arithmetic equivalence uses the separately identified written proof.')
    result=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(result)
    print(result,end='')
