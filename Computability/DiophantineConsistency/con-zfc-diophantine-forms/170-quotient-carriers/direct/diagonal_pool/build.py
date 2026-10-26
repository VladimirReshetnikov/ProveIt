#!/usr/bin/env python3
"""Compose attributed strict ranges and fixed-base pools with the new radix.

No imported producer is executed. The source delta and the local algebraic
identities are recorded explicitly; the unbounded proof is in PROOF.md.
"""
from pathlib import Path
from collections import defaultdict
import argparse,copy,hashlib,json

ROOT=Path(__file__).resolve().parent
WORK=ROOT.parent.parent

def add(*ps):
    d=defaultdict(int)
    for p in ps:
        for m,c in p.items():d[m]+=c
    return {m:c for m,c in d.items() if c}
def scale(c,p):return {m:c*v for m,v in p.items() if c*v}
def sub(p,q):return add(p,scale(-1,q))
def mul(p,q):
    d=defaultdict(int)
    for m,c in p.items():
        for n,b in q.items():d[tuple(sorted(m+n))]+=c*b
    return {m:c for m,c in d.items() if c}
def V(i):return {(i,):1}
def C(c):return {():c} if c else {}
def P(ts):return {tuple(m):c for c,m in ts if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def subst(p,mp):
    out={}
    for m,c in p.items():
        a=C(c)
        for i in m:a=mul(a,mp.get(i,V(i)))
        out=add(out,a)
    return out
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')
def export(eq,out,cert):
    poly={}
    for r in eq['residuals']:p=P(r['terms']);poly=add(poly,mul(p,p))
    met={'variables':len(eq['variables']),'rows':len(eq['residuals']),
         'degree':max(map(len,poly)),'monomials':len(poly),
         'height':max(map(abs,poly.values())),
         'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',{'domain':'unrestricted integers','variables':len(eq['variables']),'terms':terms(poly)}),('METRICS.json',met),('certificate.json',cert)]:write(out/name,obj)
    print(out.name,json.dumps(met,sort_keys=True))
    return met

def strict(parent,out):
    a=json.loads(parent.read_text());names={v['name']:i for i,v in enumerate(a['variables'])}
    rows=[P(r['terms']) for r in a['residuals']]
    oldnames=['pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1']
    removed={names[n] for n in oldnames};out6,disc,quot,ratio=[names[n] for n in oldnames]
    r0=names['remainder_budget.ratio0']
    uses={i:[j for j,r in enumerate(rows) if any(i in m for m in r)] for i in removed}
    if len(uses[quot])!=1:raise ValueError('private power quotient not unique')
    p6row=uses[quot][0]
    if set(uses[disc])!={p6row,*[j for j,r in enumerate(rows) if r==sub(V(disc),add(scale(2,V(names['shared.A'])),mul(V(names['shared.A']),V(names['shared.A']))))]}:raise ValueError('discriminant use set')
    ratio_rows=[j for j,r in enumerate(a['residuals']) if r['label']=='remainder_budget.ratio1']
    if len(ratio_rows)!=1:raise ValueError('ratio row')
    deleted_rows=set(uses[disc])|set(ratio_rows)
    frame=next(j for j,r in enumerate(a['residuals']) if r['label']=='shared.frame_definition')
    if set(uses[out6])!={p6row,frame,ratio_rows[0]}:raise ValueError('removed power output uses')
    range_rows=[j for j in uses[ratio] if j not in deleted_rows]
    if len(range_rows)!=5:raise ValueError('five strict ranges')
    keep=[i for i in range(len(a['variables'])) if i not in removed];ren={i:j for j,i in enumerate(keep)}
    result=[]
    for j,r in enumerate(rows):
        if j in deleted_rows:continue
        if j==frame:
            if r.get((out6,out6))!=-1:raise ValueError('frame term')
            r=add(r,{(out6,out6):1})
        if j in range_rows:r=subst(r,{ratio:V(r0)})
        if any(i in removed for m in r for i in m):raise ValueError('deleted variable survives')
        result.append({'label':a['residuals'][j]['label'],'terms':terms({tuple(ren[i] for i in m):c for m,c in r.items()})})
    eq={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':'strict_diagonal','variables':[a['variables'][i] for i in keep],'residuals':result}
    cert={'parent':'inputs/source238.json','parent_sha256':digest(parent),'removed_variables':sorted(removed),'removed_rows':sorted(deleted_rows),'old_to_new':sorted(ren.items()),'range_rows':range_rows,'ratio_redirect':[ratio,r0],'frame_row':frame,'removed_frame_term':[-1,[out6,out6]],'uses':uses,'attribution':'Cofinal strict local bounds and deletion of q^(t+1) from Pooled Powers, STRICT_HORIZON_AND_BETA.md Sections 1-3. The new even cofinal horizon and signed radix have a separate proof.'}
    export(eq,out,cert)
    return eq,cert

PLUS=[(3,2,'mul.503',0,0),(5,3,'mul.529',-1,0),(7,5,'mul.554',0,0),(8,6,'mul.567',0,0),(9,7,'mul.580',0,0),(10,8,'mul.593',0,0),(12,10,'mul.619',0,0),(13,11,'mul.632',0,0),(15,13,'mul.658',0,0),(16,14,'mul.671',0,0),(17,15,'mul.684',0,0)]
RADIX=[(4,0,'mul.460',0,0),(11,9,'mul.606',0,0),(14,12,'mul.645',0,1)]

def pool(parent,out):
    a=json.loads(parent.read_text());names={v['name']:i for i,v in enumerate(a['variables'])}
    rows=[P(r['terms']) for r in a['residuals']];variables=copy.deepcopy(a['variables'])
    def named(n,offset=0):return add(V(names[n]),C(offset))
    A=named('shared.A',1);q=add(scale(6,named('radix.odd_multiple_of_three_parameter')),C(3))
    def modulus(base):return sub(sub(scale(2,mul(A,base)),mul(base,base)),C(1))
    Tplus=modulus(add(q,C(1)));Tq=modulus(q);ti=names['base3.T']
    modrows=[j for j,r in enumerate(rows) if r in [sub(V(ti),Tplus),sub(Tplus,V(ti))]]
    if len(modrows)!=1:raise ValueError('base3 modulus row')
    sign=1 if rows[modrows[0]]==sub(V(ti),Tplus) else -1
    # Either orientation of the equation still stores the actual positive T.
    # The sign above records the residual orientation, not the coordinate sign.
    Tstored=V(ti)
    Tqstored=add(Tstored,sub(Tq,Tplus))
    if max(map(len,Tqstored))>1:raise ValueError('affine second modulus')
    drop_rows=set(modrows);drop_vars={ti};newrows=[];groups=[]
    for label,base,tpoly,requests in [('q_plus_one',add(q,C(1)),Tstored,PLUS),('q',q,Tqstored,RADIX)]:
        H={};S={};Y2={};records=[]
        for pno,pair,zn,ys,zs in requests:
            m=named(f'pow{pno}.output');X=named(f'index{pair}.X',1);Y=named(f'index{pair}.Y',ys);Z=named(zn,zs)
            qi=names[f'pow{pno}.quotient'];err=add(m,scale(-1,X),Z,scale(-1,mul(base,Y)))
            options=[add(err,mul(tpoly,V(qi))),sub(err,mul(tpoly,V(qi)))];options+= [scale(-1,p) for p in options]
            hits=[j for j,r in enumerate(rows) if r in options]
            if len(hits)!=1:raise ValueError(('power row',pno,hits))
            ay=sub(Z,mul(A,Y));ayhits=[j for j,r in enumerate(rows) if r==ay or r==scale(-1,ay)]
            norm=add(mul(X,X),mul(Y,Y),scale(-1,mul(Z,Z)),C(-1));nhits=[j for j,r in enumerate(rows) if r==norm or r==scale(-1,norm)]
            if len(ayhits)!=1 or len(nhits)!=1:raise ValueError(('principal pair',pno,ayhits,nhits))
            drop_rows.add(hits[0]);drop_vars.add(qi)
            H=add(H,mul(Y,sub(m,X)));D=add(m,scale(-1,X),Z);S=add(S,mul(D,D),scale(-1,mul(Y,Y)));Y2=add(Y2,mul(Y,Y))
            records.append({'request':pno,'pair':pair,'output':terms(m),'X':terms(X),'Y':terms(Y),'Z':terms(Z),'error':terms(err),'deleted_row':hits[0],'deleted_quotient':qi,'AY_row':ayhits[0],'norm_row':nhits[0]})
        ki=len(variables);li=ki+1;variables.extend([{'name':label+'.K','kind':'pooled_power'},{'name':label+'.L','kind':'pooled_power'}])
        rK=sub(sub(V(ki),scale(2,H)),mul(sub(scale(2,A),base),V(li)))
        rL=add(S,scale(-1,mul(base,V(ki))),V(li))
        newrows.extend([{'label':label+'.pooled_bilinear','terms':terms(rK)},{'label':label+'.pooled_norm','terms':terms(rL)}])
        errors={};correction={}
        for rec in records:
            errors=add(errors,mul(P(rec['error']),P(rec['error'])))
            correction=add(correction,scale(-2,mul(mul(base,P(rec['Y'])),sub(P(rec['Z']),mul(A,P(rec['Y']))))))
        rhs=add(S,scale(-2,mul(base,H)),scale(-1,mul(modulus(base),Y2)))
        if sub(errors,rhs)!=correction:raise ValueError('pooled identity')
        groups.append({'group':label,'base':terms(base),'A':terms(A),'old_modulus_expression':terms(tpoly),'T':terms(modulus(base)),'H':terms(H),'S':terms(S),'Y2':terms(Y2),'K':ki,'L':li,'requests':records,'new_rows':newrows[-2:]})
    keep=[i for i in range(len(variables)) if i not in drop_vars];ren={i:j for j,i in enumerate(keep)}
    retained=[];orig=[]
    for j,r in enumerate(a['residuals']):
        if j in drop_rows:continue
        if any(i in drop_vars for _,m in r['terms'] for i in m):raise ValueError(('deleted field remains',j))
        retained.append(r);orig.append(j)
    retained+=newrows;orig+=[None]*len(newrows)
    result=[{'label':r['label'],'terms':terms({tuple(ren[i] for i in m):c for c,m in r['terms']})} for r in retained]
    eq={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':'pooled_diagonal','variables':[variables[i] for i in keep],'residuals':result}
    cert={'parent':'../strict/equation.json','parent_sha256':digest(parent),'groups':groups,'modulus_row':modrows[0],'modulus_row_orientation':sign,'removed_variables':sorted(drop_vars),'removed_rows':sorted(drop_rows),'old_to_new':sorted(ren.items()),'new_row_parent_indices':orig,'attribution':'Two-row fixed-base pooling from Pooled Powers, POOLED_POWERS.md. Here q=6z+3 authenticates both nonunit bases before the arithmetic bootstrap.'}
    export(eq,out,cert)
    return eq,cert

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,default=ROOT/'inputs/source238.json');ap.add_argument('--output',type=Path,default=ROOT/'output');args=ap.parse_args()
    strict(args.parent,args.output/'strict')
    pool(args.output/'strict/equation.json',args.output/'pooled')

if __name__=='__main__':main()
