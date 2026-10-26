#!/usr/bin/env python3
"""Literal semantic composition of source157 and source158.

Discovery/builder. Stages are accompanied by exact row-edit and algebra
certificates. Semantic equivalence is the separate unbounded proof.
"""
from pathlib import Path
import json,sys,hashlib,copy

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'158-pooled-powers/code'))
import build_pools as P
import build_basis as B
import shear_pell as D

def read(p): return json.loads(p.read_bytes())
def poly(r): return {tuple(m):c for c,m in r['terms']}
def write(p,o):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(o,sort_keys=True,separators=(',',':'))+'\n')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def export(out,e,cname,cert):
    ps=[poly(r) for r in e['residuals']]
    ex=B.add(*(B.mul(p,p) for p in ps))
    metrics={'variables':len(e['variables']),'rows':len(ps),'degree':max(map(len,ex)),
        'monomials':len(ex),'height':max(map(abs,ex.values())),
        'row_height':max(abs(c) for p in ps for c in p.values())}
    for name,obj in [('equation.json',e),('METRICS.json',metrics),
        ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','domain':'unrestricted integers','variables':len(e['variables']),'terms':B.terms(ex)}),
        (cname,cert)]:write(out/name,obj)
    print(out.name,metrics,flush=True)

def strict(parent,out):
    a=read(parent);n={v['name']:i for i,v in enumerate(a['variables'])}
    removed_names=['pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1']
    rm={n[s] for s in removed_names};p6=n['pow6.output'];ratio1=n['remainder_budget.ratio1'];ratio0=n['remainder_budget.ratio0']
    uses={i:[j for j,r in enumerate(a['residuals']) if any(i in m for _,m in r['terms'])] for i in rm}
    framed=[j for j,r in enumerate(a['residuals']) if r['label']=='shared.frame_definition']
    if len(framed)!=1:raise ValueError('one frame')
    frame=framed[0]
    removed_rows=set(uses[n['index_addition.D']])|set(uses[n['pow6.quotient']])
    ratios=[j for j,r in enumerate(a['residuals']) if r['label']=='remainder_budget.ratio1']
    if len(ratios)!=1:raise ValueError('one removed ratio')
    removed_rows.add(ratios[0])
    if len(removed_rows)!=3:raise ValueError('three removed rows')
    labels={'crt.range.a.quotient_multiple','crt.range.b.quotient_multiple','crt.range.c.quotient_multiple','crt.range.d.quotient_multiple','crt.range.derived_label_sum.quotient_multiple'}
    changed=[j for j,r in enumerate(a['residuals']) if r['label'] in labels]
    if len(changed)!=5:raise ValueError('five strict ranges')
    old_new=[];rows=[];origins=[]
    for j,r in enumerate(a['residuals']):
        if j in removed_rows:continue
        p=poly(r)
        if j==frame:
            if p.pop((p6,p6),None)!=-1:raise ValueError('exact removed frame atom')
        if j in changed:p=B.subst(p,{ratio1:B.var(ratio0)})
        if any(i in rm for m in p for i in m):raise ValueError(('residual use',j))
        rr=dict(r,terms=B.terms(p));rows.append(rr);origins.append(j)
        if rr!=r:old_new.append({'row':j,'old':r,'new':rr})
    keep=[i for i in range(len(a['variables'])) if i not in rm];ren={i:j for j,i in enumerate(keep)}
    e=dict(a,variables=[a['variables'][i] for i in keep],residuals=[dict(r,terms=[[c,[ren[i] for i in m]] for c,m in r['terms']]) for r in rows],variant='factorial_free_strict238',parent_sha256=sha(parent))
    cert={'source':'157 source equation','parent_sha256':sha(parent),'removed_variables':sorted(rm),'removed_names':removed_names,'removed_rows':sorted(removed_rows),'edits':old_new,'uses':uses,'old_to_new':list(ren.items()),'row_origins':origins,'semantic_change':'Five cofinal strict parameter/derived-label ranges t+1 to t; remove q^(t+1) request and redirect its ratio.'}
    export(out,e,'strict_certificate.json',cert)

def basis(parent,out):
    a=read(parent);old=read(ROOT/'158-pooled-powers/inputs/parent245.json')
    names={z['name']:i for i,z in enumerate(a['variables'])};ns=len(a['variables'])
    ids={i:names[z['name']] for i,z in enumerate(old['variables']) if z['name'] in names}
    ids[3]=names['crt.growth_majorant_F']
    # The inherited local Horn circuit is byte-for-byte equal after this name map.
    def p(i):return B.var(ids[i]) if i!=245 else B.var(ns)
    def remap(r):return {tuple(sorted(ids[i] for i in m)):c for c,m in r['terms']}
    rows=[poly(r) for r in a['residuals']];match={}
    for j in [54,65,67,68,69,70,72,73,74]:
        target=remap(old['residuals'][j]);hits=[i for i,r in enumerate(rows) if r==target]
        if len(hits)!=1:raise ValueError(('unique Horn match',j,hits))
        match[j]=hits[0]
    F,S,Sp,aa,bb,s,K,J=[p(i) for i in (3,14,15,10,11,21,70,245)]
    g=B.sub(B.sub(S,Sp),p(82));d=B.add(B.scalar(6,aa),B.scalar(8,bb),B.scalar(2,s));lower=B.sub(aa,B.num(1))
    rm={ids[i] for i in [83,84,85,89]};rmrows={match[j] for j in [67,68,70,73]}
    edits={match[65]:B.sub(B.sub(p(81),B.mul(p(80),p(80))),B.mul(g,g)),
        match[69]:B.add(B.neg(Sp),B.neg(B.mul(K,bb)),B.mul(p(86),p(87)),p(88)),
        match[72]:B.add(B.neg(S),B.neg(B.mul(J,lower)),p(87)),
        match[74]:B.add(S,B.mul(J,bb),B.neg(Sp),B.neg(B.mul(K,d)),p(90))}
    newJ=B.sub(J,B.mul(F,S));newrows=[];origins=[]
    for j,r in enumerate(rows):
        if j in rmrows:continue
        q=edits.get(j,{m:c for m,c in r.items() if ids[83] not in m})
        if any(i in rm for m in q for i in m):raise ValueError(('private wire remained',j))
        newrows.append(q);origins.append(j)
    newrows.append(newJ);origins.append(None)
    reverse={ids[81]:B.mul(p(80),p(80)),ids[83]:B.sub(p(81),B.mul(p(80),p(80))),
        ids[84]:B.add(B.num(1),B.mul(F,bb)),ids[85]:B.add(B.num(1),B.mul(F,lower)),ids[89]:B.add(B.num(1),B.mul(F,d))}
    restored=[B.subst(r,reverse) for r in rows]
    revtarget={match[67]:edits[match[65]],match[69]:B.add(edits[match[69]],B.mul(bb,rows[match[54]])),
        match[72]:B.add(edits[match[72]],B.mul(lower,newJ)),
        match[74]:B.add(edits[match[74]],B.neg(B.mul(bb,newJ)),B.mul(d,rows[match[54]]))}
    deleted0={match[j] for j in [65,68,70,73]}
    for j,r in enumerate(restored):
        exp={} if j in deleted0 else revtarget.get(j,next((z for z,k in zip(newrows,origins) if k==j),None))
        if r!=exp:raise ValueError(('reverse identity',j))
    forward={ids[81]:B.add(p(81),p(83)),ns:B.mul(F,S)}
    for nr,j in zip(newrows,origins):
        fr=B.subst(nr,forward)
        if j is None:exp={}
        elif j==match[65]:exp=B.add(rows[match[65]],rows[match[67]])
        elif j==match[69]:exp=B.add(rows[j],B.mul(Sp,rows[match[68]]),B.neg(B.mul(bb,rows[match[54]])))
        elif j==match[72]:exp=B.add(rows[j],B.mul(S,rows[match[70]]))
        elif j==match[74]:exp=B.add(rows[j],B.neg(B.mul(S,rows[match[68]])),B.mul(Sp,rows[match[73]]),B.neg(B.mul(d,rows[match[54]])))
        else:exp=rows[j]
        if fr!=exp:raise ValueError(('forward identity',j))
    variables=copy.deepcopy(a['variables'])+[{'kind':'shared_product','name':'horn.F_times_S'}]
    variables[ids[81]]={'kind':'rank_aggregate','name':'horn.joint_square_sum'}
    keep=[i for i in range(ns+1) if i not in rm];ren={i:j for j,i in enumerate(keep)}
    rs=[{'label':a['residuals'][j]['label'] if j is not None else 'shared F times S','terms':[[c,[ren[i] for i in m]] for c,m in B.terms(q)]} for q,j in zip(newrows,origins)]
    e=dict(a,variables=[variables[i] for i in keep],residuals=rs,variant='factorial_free_consumer235',parent_sha256=sha(parent))
    cert={'parent_sha256':sha(parent),'parent158_sha256':sha(ROOT/'158-pooled-powers/inputs/parent245.json'),'matched_rows':list(match.items()),'name_map':list(ids.items()),'removed_variables':sorted(rm),'removed_rows':sorted(rmrows),'edits':[[j,B.terms(q)] for j,q in sorted(edits.items())],'forward':[[i,B.terms(q)] for i,q in forward.items()],'reverse':[[i,B.terms(q)] for i,q in reverse.items()],'old_to_new':list(ren.items()),'row_origins':origins,'forward_identities':len(newrows),'reverse_identities':len(rows)}
    export(out,e,'basis_certificate.json',cert)

def main():
    out=ROOT/'composed'
    source=ROOT/'157-linear-crt/source/equation.json'
    strict(source,out/'strict238')
    basis(out/'strict238/equation.json',out/'basis235')
    P.main(out/'basis235/equation.json',out/'pooled223')
    # Preserve the historical producer attribution without mislabelling the
    # newly composed equation's actual comparison snapshot.
    poolpath=out/'pooled223/equation.json';pooled=read(poolpath)
    pooled['inherited_producer_source_commit']=pooled['source_commit']
    pooled['source_commit']='953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4'
    write(poolpath,pooled)
    D.main(out/'pooled223/equation.json',out/'differences223')

if __name__=='__main__':main()
