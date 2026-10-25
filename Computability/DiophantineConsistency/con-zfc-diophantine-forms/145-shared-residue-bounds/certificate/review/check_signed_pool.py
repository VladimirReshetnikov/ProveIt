#!/usr/bin/env python3
"""Independent projection, translation and exact SOS census for signed pools.
Does not import the producer, inherited compiler, or its polynomial library.
"""
from pathlib import Path
from collections import defaultdict
import json, hashlib, argparse
BASE=Path(__file__).resolve().parents[1]
OUT=Path(__file__).resolve().parent
PARENT=BASE/'parent'/'strict_dimension'

def req(b,msg):
    if not b: raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def poly(ts):
    q=defaultdict(int)
    for c,m in ts:q[tuple(sorted(m))]+=c
    return {m:c for m,c in q.items() if c}
def add(p,q):
    r=defaultdict(int,p)
    for m,c in q.items():r[m]+=c
    return {m:c for m,c in r.items() if c}
def mul(p,q):
    r=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}
def sub(p,mapping):
    r={}
    for m,c in p.items():
        term={():c}
        for i in m:term=mul(term,mapping.get(i,{(i,):1}))
        r=add(r,term)
    return r

def source_delta(d):
    parent=read(PARENT/'guarded.json'); out=read(d/'source.json')
    ns={v['name']:i for i,v in enumerate(parent['variables'])}
    triples=[('choose0.remainder','choose0.rslack','pow4.output'),
             ('range8.remainder','range8.slack','pow4.output')]
    triples += [(f'range{i}.remainder',f'range{i}.slack','pow6.output') for i in [0,1,2,3,9]]
    triples += [(f'range{i}.remainder',f'range{i}.slack','pow11.output') for i in [4,5]]
    triples += [(f'range{i}.remainder',f'range{i}.slack','pow14.output') for i in [6,7]]
    req(out['variables'][:len(parent['variables'])]==parent['variables'],'parent variable prefix')
    dels=set()
    for r,s,L in triples:
        a,b,c=ns[r],ns[s],ns[L]
        expected={():-1,(a,):-1,(b,):-1,(c,):1}
        matches=[i for i,row in enumerate(parent['residuals']) if poly(row['terms'])==expected]
        req(len(matches)==1,'bound row unique')
        dels.update(matches)
        pair=tuple(sorted((a,b)))
        matches=[i for i,row in enumerate(parent['residuals']) if row['label'].startswith('domain_guard.') and poly(row['terms']).get(pair)==1]
        req(len(matches)==1,'guard row unique')
        gi=matches[0]; gp=poly(parent['residuals'][gi]['terms'])
        guards={j for m in gp for j in m}-{a,b}
        req(len(guards)==3,'ternary arity')
        linear=[m[0] for m,co in gp.items() if len(m)==1 and co==-1]
        req(len(linear)==1 and linear[0] in guards,'ternary linear')
        ep={pair:1,(linear[0],):-1}
        ep.update({(j,j):-1 for j in guards})
        req(ep==gp,'ternary exact polynomial')
        dels.add(gi)
    req(len(dels)==22,'exactly eleven intervals')
    kept=[r for i,r in enumerate(parent['residuals']) if i not in dels]
    req(out['residuals'][:len(kept)]==kept,'unchanged parent row prefix')
    # Authenticate that the old Horn factorization is literally the parent map,
    # only with its newly allocated root variable renamed.
    pc=read(PARENT/'factorization_certificate.json'); nc=read(d/'factorization_certificate.json')
    rootmap={pc['new_root']:nc['new_root']}
    pc['new_root']=nc['new_root']
    pc['new_row']=[[co,[rootmap.get(i,i) for i in m]] for co,m in pc['new_row']]
    for ch in pc['changes']:
        ch['new']=[[co,[rootmap.get(i,i) for i in m]] for co,m in ch['new']]
    for k in pc:
        if k not in ('input_sha256','output_sha256'):req(pc[k]==nc[k],f'inherited Horn factorization {k}')
    # Independently construct each new norm row using variable names.
    newns={v['name']:i for i,v in enumerate(out['variables'])}
    groups={ns['pow4.output']:[ns['choose0.remainder'],ns['range8.remainder']],
            ns['pow6.output']:[ns[f'range{i}.remainder'] for i in [0,1,2,3,9]],
            ns['pow11.output']:[ns[f'range{i}.remainder'] for i in [4,5]],
            ns['pow14.output']:[ns[f'range{i}.remainder'] for i in [6,7]]}
    tail=out['residuals'][len(kept):]; expected=[]
    merged=d.name=='merged_aggregate'
    if merged:
        r0,r8=groups.pop(ns['pow4.output']); summ=newns['residue_pool.small_squares']
        expected.append({(summ,):1,(r0,r0):-1,(r8,r8):-1})
        q=ns['pow2.output']; q2=ns['mul.520']
        req(any(poly(r['terms'])=={(q2,):1,(q,q):-1} for r in kept),'literal q square')
    for gi,(L,rs) in enumerate(groups.items()):
        a,b,c=[newns[f'residue_pool{gi}.{n}'] for n in ('a','b','c')]
        ep={(L,L):1,():-1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
        ep.update({(r,r):-2 for r in rs})
        if merged and L==ns['pow6.output']:ep[tuple(sorted((q2,summ)))]=-2
        expected.append(ep)
    req([poly(r['terms']) for r in tail]==expected,'exact new caps')
    return {'deleted_interval_rows':22,'new_rows':len(tail),'all_other_parent_rows_identical':True,'inherited_Horn_factorization_identical_after_root_rename':True}

def projection(d):
    src=read(d/'factored_source.json'); pc=read(d/'projection_certificate.json'); out=read(d/'projected.json')
    rows={i:poly(r['terms']) for i,r in enumerate(src['residuals'])}
    removed=set()
    for ix,s in enumerate(pc['steps']):
        v=s['variable']; rid=s['row_id']; rest=poly(s['restoration']); row=rows[rid]
        req(v not in removed,'repeated elimination')
        req(all(v not in m for m in rest),'self-referential restoration')
        unit=row.get((v,),0)
        req(unit in (-1,1),'nonunit pivot')
        expect={(v,):unit}
        expect=add(expect,{m:-unit*c for m,c in rest.items()})
        req(row==expect,f'pivot mismatch {ix}')
        del rows[rid]
        for j,p in list(rows.items()):
            if any(v in m for m in p):rows[j]=sub(p,{v:rest})
            req(max(map(len,rows[j]),default=0)<=2,'nonquadratic intermediate')
        removed.add(v)
    keep=pc['retained_original_variables']; remap={v:i for i,v in enumerate(keep)}
    req(list(rows)==pc['retained_original_rows'],'retained rows')
    req(len(rows)==len(out['residuals']),'output rows')
    used=set(i for p in rows.values() for m in p for i in m)
    req(used==set(keep),'retained variables')
    unused=set(range(len(src['variables'])))-removed-used
    req(unused==set(pc['unconstrained_removed']),'unconstrained deletion')
    for (rid,p),r in zip(rows.items(),out['residuals']):
        renamed={tuple(sorted(remap[i] for i in m)):c for m,c in p.items()}
        req(renamed==poly(r['terms']),f'projected row {rid}')
        req(src['residuals'][rid]['label']==r['label'],'label mismatch')
    return {'eliminations':len(removed),'unconstrained':len(unused),'rows':len(rows),'variables':len(keep)}

def endpoint(d):
    src=read(d/'projected.json'); cert=read(d/'translation_certificate.json'); end=read(d/'equation.json')
    mapping={i:{(i,):1,():s} for i,s in cert['shifts']}
    req(len(src['residuals'])==len(end['residuals']),'translation row count')
    total={};used=set();maxrow=0
    for i,(s,r) in enumerate(zip(src['residuals'],end['residuals'])):
        p=poly(r['terms'])
        req(sub(poly(s['terms']),mapping)==p,f'translation row {i}')
        req(max(map(len,p),default=0)<=2,'final nonquadratic row')
        used.update(j for m in p for j in m)
        maxrow=max(maxrow,max(map(abs,p.values())))
        total=add(total,mul(p,p))
    req(total==poly(read(d/'expanded_polynomial.json')['terms']),'collected SOS mismatch')
    req(used==set(range(len(end['variables']))),'nonlive coordinate')
    met={'variables':len(used),'rows':len(end['residuals']),'degree':max(map(len,total)),'monomials':len(total),'height':max(map(abs,total.values())),'row_height':maxrow}
    req(met==read(d/'METRICS.json'),'metrics mismatch')
    met['equation_sha256']=hashlib.sha256((d/'equation.json').read_bytes()).hexdigest()
    return met

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=BASE,help='directory containing grouped and merged_aggregate endpoints')
    parser.add_argument('--parent',type=Path,default=PARENT,help='directory containing the parent strict_dimension source')
    parser.add_argument('--output',type=Path,default=OUT/'SIGNED_POOL_INDEPENDENT_CHECK.json')
    args=parser.parse_args(); BASE=args.base.resolve(); PARENT=args.parent.resolve()
    result={}
    for name in ['grouped','merged_aggregate']:
        result[name]={'source_delta':source_delta(BASE/name),'projection':projection(BASE/name),'centered':endpoint(BASE/(name+'_centered'))}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
