#!/usr/bin/env python3
"""Independent literal, frame and pooled-identity audit. No producer import."""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,copy,hashlib,json

ROOT=Path(__file__).resolve().parent
PARENT_SHA='f210bfc93e5102c1a6411950607f721a652b03142828c4309fd5923e1d6b75d7'

def require(x,msg):
    if not x:raise ValueError(msg)
def load(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(ts):
    r=defaultdict(int)
    for c,m in ts:r[tuple(sorted(m))]+=c
    return {m:c for m,c in r.items() if c}
def plus(*ps):
    q=defaultdict(int)
    for p in ps:
        for m,c in p.items():q[m]+=c
    return {m:c for m,c in q.items() if c}
def times(p,q):
    r=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}
def sc(c,p):return {m:c*d for m,d in p.items() if c*d}
def var(i):return {(i,):1}
def const(c):return {():c} if c else {}
def minus(p,q):return plus(p,sc(-1,q))
def sub(p,mp):
    r={}
    for m,c in p.items():
        term=const(c)
        for i in m:term=times(term,mp.get(i,var(i)))
        r=plus(r,term)
    return r
def renumber(p,mp):return {tuple(mp[i] for i in m):c for m,c in p.items()}

def source_check(parent,out):
    require(sha(parent)==PARENT_SHA,'pinned source238 bytes')
    a=load(parent);rows=[norm(r['terms']) for r in a['residuals']];names={v['name']:i for i,v in enumerate(a['variables'])}
    s=load(out/'strict/equation.json');cert=load(out/'strict/certificate.json')
    require(cert['parent_sha256']==PARENT_SHA,'strict parent binding')
    drop={names[n] for n in ['pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1']}
    require(drop==set(cert['removed_variables']),'exact four removed coordinates')
    frame=next(i for i,r in enumerate(a['residuals']) if r['label']=='shared.frame_definition')
    out6,disc,quot,ratio=[names[n] for n in ['pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1']]
    uses=lambda i:[j for j,r in enumerate(rows) if any(i in m for m in r)]
    require(len(uses(quot))==1,'private pow6 quotient')
    p6=uses(quot)[0];dr=next(j for j in uses(disc) if j!=p6)
    rr=next(j for j,r in enumerate(a['residuals']) if r['label']=='remainder_budget.ratio1')
    require(set(uses(disc))=={dr,p6},'private discriminant')
    require(set(uses(out6))=={p6,frame,rr},'private output')
    deleted={dr,p6,rr};require(deleted==set(cert['removed_rows']),'exact deleted rows')
    ar=plus(var(names['shared.A']),const(1));q=plus(sc(6,var(names['radix.odd_multiple_of_three_parameter'])),const(3))
    delta=minus(times(ar,ar),const(1));require(rows[dr]==minus(var(disc),delta),'derived discriminant definition')
    X=plus(var(names['index0.X']),const(1));Y=var(names['index0.Y']);Z=var(names['mul.460'])
    Tq=plus(var(names['base3.T']),sc(2,q),sc(-2,ar),const(1))
    e6=plus(var(out6),times(ar,Z),sc(-1,times(var(disc),Y)),sc(-1,times(q,plus(X,Z))))
    options=[plus(e6,times(Tq,var(quot))),minus(e6,times(Tq,var(quot)))];options+=[sc(-1,p) for p in options]
    require(rows[p6] in options,'exact deleted derived-power row')
    M=var(names['pow14.output']);ratioeq=minus(M,times(var(out6),var(ratio)))
    require(rows[rr] in [ratioeq,sc(-1,ratioeq)],'deleted normalization ratio')
    range_rows=set(uses(ratio))-{rr};require(len(range_rows)==5 and range_rows==set(cert['range_rows']),'five actual tightened ranges')
    keep=[i for i in range(len(a['variables'])) if i not in drop];mp={i:j for j,i in enumerate(keep)}
    require(dict(cert['old_to_new'])==mp,'strict reindex map')
    expected=[]
    for j,r in enumerate(rows):
        if j in deleted:continue
        if j==frame:
            require(r.get((out6,out6))==-1,'removed output square');r=plus(r,{(out6,out6):1})
        if j in range_rows:r=sub(r,{ratio:var(names['remainder_budget.ratio0'])})
        require(not any(i in drop for m in r for i in m),'deleted occurrence remains')
        expected.append(renumber(r,mp))
    require([norm(r['terms']) for r in s['residuals']]==expected,'entire strict residual system')
    require(s['variables']==[a['variables'][i] for i in keep],'strict coordinate metadata')
    return a,s,mp

def frame_check(parent,strict,strictmap,affine):
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    v=lambda n:var(names[n])
    t=v('t0');x=v('x');yp=v('y');F=v('crt.growth_majorant_F');q=plus(sc(6,v('radix.odd_multiple_of_three_parameter')),const(3))
    ac=load(affine);removed={p['variable'] for p in ac['projections']};oldn=len(parent['variables'])+len(removed)
    oldmap={i:j for j,i in enumerate(i for i in range(oldn) if i not in removed)}
    jp=next(p for p in ac['projections'] if p['name']=='add.380');J=renumber(norm(jp['replacement']),oldmap)
    reps=[plus(v('crt.encoded.a'),const(-1))]+[v(n) for n in ['crt.encoded.b','crt.encoded.c','crt.encoded.d','crt.encoded.S','crt.encoded.Sp','crt.encoded.u','crt.encoded.vq','crt.encoded_index_minus_one']]
    plusreq=[3,5,7,8,9,10,12,13,15,16,17];qreq=[4,11,14]
    atoms=[t,x,yp,F,plus(F,t),plus(t,const(1)),v('choose0.output'),v('pow1.output'),*reps,J,q,plus(q,const(1)),*[v(f'pow{p}.output') for p in plusreq+qreq],t,v('self_radix.BH')]
    require(len(atoms)==36,'36 retained frame atoms')
    atoms=[renumber(p,strictmap) for p in atoms]
    snames={v['name']:i for i,v in enumerate(strict['variables'])};W=var(snames['shared.W'])
    expected=minus(W,const(2))
    for p in atoms:expected=minus(expected,times(p,p))
    frame=next(r for r in strict['residuals'] if r['label']=='shared.frame_definition')
    require(norm(frame['terms'])==expected,'complete exact sum-of-affine-squares frame')
    def actual(p):return renumber(p,strictmap)
    exponent=[plus(F,t),*reps[:6],reps[6],reps[7],reps[8],J]
    # Explicit matching avoids silently changing the number/order of requests.
    exponent=[plus(F,t),reps[0],reps[1],reps[2],reps[3],reps[4],reps[5],reps[6],reps[7],reps[8],J]
    requests=[]
    for p,k in zip(plusreq,exponent):requests.append((p,actual(plus(q,const(1))),actual(v(f'pow{p}.output')),actual(k)))
    for p,k in zip(qreq,[t,yp,x]):requests.append((p,actual(q),actual(v(f'pow{p}.output')),actual(k)))
    requests += [(0,actual(t),actual(F),actual(t)),(1,actual(v('choose0.output')),actual(v('pow1.output')),actual(x)),(2,actual(v('self_radix.BH')),actual(q),actual(x))]
    for p,*ps in requests:
        for a in ps:require(a in atoms,('unframed actual atom',p))
    return {'affine_squares':36,'all_retained_requests':17,'pooled_requests':14,'frame_identity':True,'all_actual_atoms_checked':True}

def pool_check(strict,out):
    parent=out/'strict/equation.json';p=load(out/'pooled/equation.json');cert=load(out/'pooled/certificate.json')
    require(cert['parent_sha256']==sha(parent),'pool parent binding')
    rows=[norm(r['terms']) for r in strict['residuals']];names={v['name']:i for i,v in enumerate(strict['variables'])}
    A=plus(var(names['shared.A']),const(1));q=plus(sc(6,var(names['radix.odd_multiple_of_three_parameter'])),const(3))
    def T(n):return plus(sc(2,times(A,n)),sc(-1,times(n,n)),const(-1))
    ti=names['base3.T'];modrow=cert['modulus_row'];require(rows[modrow] in [minus(var(ti),T(plus(q,const(1)))),minus(T(plus(q,const(1))),var(ti))],'literal retained modulus')
    droprows={modrow};dropvars={ti};new=[];expected_requests=[[3,5,7,8,9,10,12,13,15,16,17],[4,11,14]]
    require(len(cert['groups'])==2,'exact two pools')
    for gi,g in enumerate(cert['groups']):
        base=plus(q,const(1)) if gi==0 else q;oldT=var(ti) if gi==0 else plus(var(ti),sc(2,q),sc(-2,A),const(1))
        require(norm(g['base'])==base and norm(g['A'])==A and norm(g['T'])==T(base),'actual pooled base and modulus')
        require([r['request'] for r in g['requests']]==expected_requests[gi],'exact request family')
        H={};S={};Y2={};Err={};correction={}
        for r in g['requests']:
            m,X,Y,Z=[norm(r[k]) for k in ['output','X','Y','Z']]
            pno=r['request'];pair=r['pair'];ys=-1 if pair==3 else 0;zs=1 if pair==12 else 0
            require(m==var(names[f'pow{pno}.output']) and X==plus(var(names[f'index{pair}.X']),const(1)) and Y==plus(var(names[f'index{pair}.Y']),const(ys)),'literal coordinate offsets')
            AY=minus(Z,times(A,Y));require(rows[r['AY_row']] in [AY,sc(-1,AY)],'retained AY relation')
            normeq=plus(times(X,X),times(Y,Y),sc(-1,times(Z,Z)),const(-1));require(rows[r['norm_row']] in [normeq,sc(-1,normeq)],'retained Pell norm')
            quotient=names[f'pow{pno}.quotient'];require(r['deleted_quotient']==quotient,'private quotient identity')
            e=plus(m,sc(-1,X),Z,sc(-1,times(base,Y)));opts=[plus(e,times(oldT,var(quotient))),minus(e,times(oldT,var(quotient)))];opts+=[sc(-1,a) for a in opts]
            require(rows[r['deleted_row']] in opts,'exact removed congruence')
            droprows.add(r['deleted_row']);dropvars.add(quotient)
            H=plus(H,times(Y,minus(m,X)));D=plus(m,sc(-1,X),Z);S=plus(S,times(D,D),sc(-1,times(Y,Y)));Y2=plus(Y2,times(Y,Y));Err=plus(Err,times(e,e));correction=plus(correction,sc(-2,times(times(base,Y),AY)))
        require(norm(g['H'])==H and norm(g['S'])==S and norm(g['Y2'])==Y2,'full pooled accumulators')
        require(minus(Err,plus(S,sc(-2,times(base,H)),sc(-1,times(T(base),Y2))))==correction,'whole polynomial error identity')
        K,L=g['K'],g['L'];require((K,L)==(len(strict['variables'])+2*gi,len(strict['variables'])+2*gi+1),'fresh pool coordinates')
        new.extend([plus(var(K),sc(-2,H),sc(-1,times(minus(sc(2,A),base),var(L)))),plus(S,sc(-1,times(base,var(K))),var(L))])
    require(set(cert['removed_rows'])==droprows and set(cert['removed_variables'])==dropvars,'exact pool deletions')
    oldn=len(strict['variables']);keep=[i for i in range(oldn+4) if i not in dropvars];mp={i:j for j,i in enumerate(keep)};require(dict(cert['old_to_new'])==mp,'pool coordinate map')
    expected=[]
    for j,r in enumerate(rows):
        if j in droprows:continue
        require(not any(i in dropvars for m in r for i in m),'deleted field survives');expected.append(renumber(r,mp))
    expected += [renumber(r,mp) for r in new]
    require([norm(r['terms']) for r in p['residuals']]==expected,'entire pooled source')
    require(len(p['variables'])==223 and len(expected)==160,'literal 223/160 census')
    return p

def expansion_check(eq,directory):
    polys=[norm(r['terms']) for r in eq['residuals']];total=defaultdict(int)
    for p in polys:
        entries=list(p.items())
        for i,(a,c) in enumerate(entries):
            for j in range(i,len(entries)):
                b,d=entries[j];total[tuple(sorted(a+b))]+=(1 if i==j else 2)*c*d
    total={m:c for m,c in total.items() if c};stored=load(directory/'expanded_polynomial.json')
    require(norm(stored['terms'])==total,'every expanded coefficient')
    live={i for p in polys for m in p for i in m};require(live==set(range(len(eq['variables']))),'full coordinate liveness')
    met={'variables':len(eq['variables']),'rows':len(polys),'degree':max(map(len,total)),'monomials':len(total),'height':max(map(abs,total.values())),'row_height':max(abs(c) for p in polys for c in p.values())}
    require(load(directory/'METRICS.json')==met,'independent metric census')
    return met

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,default=ROOT/'inputs/source238.json');ap.add_argument('--output',type=Path,default=ROOT/'output');ap.add_argument('--receipt',type=Path,default=ROOT/'CHECK.json');args=ap.parse_args()
    a,s,mp=source_check(args.parent,args.output);frame=frame_check(a,s,mp,ROOT/'inputs/source238_affine_certificate.json');p=pool_check(s,args.output)
    sm=expansion_check(s,args.output/'strict');pm=expansion_check(p,args.output/'pooled')
    receipt={'result':'PASS','parent_sha256':PARENT_SHA,'strict':sm,'pooled':pm,'frame':frame,'ordinary_proof':'PROOF.md','producer_imported':False,'finite_checks_are_not_unbounded_semantic_proof':True}
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,sort_keys=True))

if __name__=='__main__':main()
