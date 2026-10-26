#!/usr/bin/env python3
"""Literal five-base oriented reciprocal pooling, with exact inherited projections.

New theorem is in ORIENTED_POOLING.md. This is a finite coefficient producer,
not an end-to-end formal proof or a search for a consistency witness.
"""
from pathlib import Path
import json, hashlib, argparse
ROOT=Path(__file__).resolve().parent

def load(p): return json.loads(p.read_text())
def readterms(ts): return {tuple(m):c for c,m in ts if c}
def terms(p): return [[c,list(m)] for m,c in sorted(p.items()) if c]
def c(a): return {():a} if a else {}
def v(i): return {(i,):1}
def add(*ps):
    z={}
    for p in ps:
        for m,a in p.items(): z[m]=z.get(m,0)+a
    return {m:a for m,a in z.items() if a}
def scale(p,a): return {m:a*b for m,b in p.items() if a*b}
def sub(p,q): return add(p,scale(q,-1))
def mul(p,q):
    z={}
    for m,a in p.items():
        for n,b in q.items():
            k=tuple(sorted(m+n));z[k]=z.get(k,0)+a*b
    return {m:a for m,a in z.items() if a}
def square(p): return mul(p,p)
def degree(p): return max((len(m) for m in p),default=-1)
def prod(ps):
    z=c(1)
    for p in ps:z=mul(z,p)
    return z
def subst(p,i,q):
    if not any(i in m for m in p):return dict(p)
    z={}
    for m,a in p.items():
        if i not in m:z[m]=z.get(m,0)+a;continue
        mon={tuple(j for j in m if j!=i):a}
        for k in range(m.count(i)):mon=mul(mon,q)
        for n,b in mon.items():z[n]=z.get(n,0)+b
    return {m:a for m,a in z.items() if a}
def deriv(p,i):
    z={}
    for m,a in p.items():
        k=m.count(i)
        if k:
            n=list(m);n.remove(i);z[tuple(n)]=a*k
    return z
def dd(p,d):return add(*(scale(deriv(p,i),a) for i,a in d.items()))
def renumber(p,mp):return {tuple(mp[i] for i in m):a for m,a in p.items()}
def must(x,message):
    if not x:raise ValueError(message)
def write(p,x):p.write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')

def build(out,split=False):
    src=ROOT/'173-crt-index-anchor-215/source/anchor221/equation.json'
    old=load(src);rows=[readterms(r['terms']) for r in old['residuals']]
    variables=list(old['variables']);labels=[r['label'] for r in old['residuals']]
    private={145,146,147,148,149,150,215,216,217,218}
    deleted={102,103,104,105,106,107,153,154,155,156}
    for i,row in enumerate(rows):
        if i not in deleted:must(not any(j in private for m in row for j in m),f'Private coordinate escapes in row {i}')
    # All expressions below use the unchanged 221-coordinate parent chart.
    A=add(v(138),c(1));bases=[v(0),v(3),v(190),sub(v(101),c(1)),v(101)]
    singles=[(v(2),v(187),v(188),v(189)),
             (v(17),v(178),v(179),add(v(180),c(1))),
             (sub(v(101),c(1)),v(178),v(179),add(v(180),c(1)))]
    Es=[];identities=[]
    for n,(m,D,Y,Z) in zip(bases,singles):
        T=sub(sub(scale(mul(A,n),2),square(n)),c(1))
        S=sub(square(sub(m,D)),square(Y))
        H=mul(Y,sub(sub(m,D),Z))
        E=sub(S,scale(mul(n,H),2));Es.append(E)
        delta=sub(sub(m,D),mul(n,Y))
        # E=delta^2+T Y^2 modulo the retained Z=A Y row.
        err=sub(sub(E,square(delta)),mul(T,square(Y)))
        target=scale(mul(mul(n,Y),sub(Z,mul(A,Y))),2)
        must(err==target,'Singleton Pell error identity')
        identities.append({'difference':terms(err),'ay_factor':terms(target)})
    for n,k,l,r0,r1 in [(bases[3],217,218,155,156),(bases[4],215,216,153,154)]:
        hrow=subst(subst(rows[r0],k,{}),l,{})
        srow=subst(subst(rows[r1],k,{}),l,{})
        E=add(srow,mul(n,hrow));Es.append(E)
        T=sub(sub(scale(mul(A,n),2),square(n)),c(1))
        must(add(rows[r1],mul(n,rows[r0]))==sub(E,mul(T,v(l))),'Pooled elimination identity')
    Ts=[sub(sub(scale(mul(A,n),2),square(n)),c(1)) for n in bases]
    plus_rows=[(102,151,152,153,0,0),(107,154,155,156,-1,0),
      (110,157,158,159,0,0),(113,160,161,162,0,0),(116,163,164,165,0,0),
      (119,166,167,168,0,0),(123,172,173,174,0,0),(126,175,176,177,0,0),
      (131,181,182,183,0,0),(134,184,185,186,0,0)]
    q_rows=[(103,142,143,144,0,0),(120,169,170,171,0,0),(127,178,179,180,0,1)]
    def requests(table):return [(v(m),v(d),add(v(y),c(yo)),add(v(z),c(zo))) for m,d,y,z,yo,zo in table]
    request_blocks=[[singles[0]],[singles[1]],[singles[2]],requests(q_rows),requests(plus_rows)]
    for n,E,block in zip(bases,Es,request_blocks):
        direct=add(*(sub(sub(square(sub(m,D)),square(Y)),scale(mul(mul(n,Y),sub(sub(m,D),Z)),2)) for m,D,Y,Z in block))
        must(direct==E,'Readable request-table mismatch')
    # All ports are transported into final coordinate charts for a short,
    # fully literal factored formula independent of the large R expansion.
    ports=[A];blocks=[]
    for n,E,T,block in zip(bases,Es,Ts,request_blocks):
        rec={'n':len(ports),'E':len(ports)+1,'T':len(ports)+2,'requests':[]};ports.extend([n,E,T])
        for req in block:rec['requests'].append(list(range(len(ports),len(ports)+4)));ports.extend(req)
        blocks.append(rec)
    zidx=len(variables);variables.append({'name':'oriented_pool.integrality_quotient','kind':'signed_witness'})
    if split:
        group=Ts[:3]
        R=sub(add(*(mul(mul(bases[i],Es[i]),prod(group[:i]+group[i+1:])) for i in range(3))),mul(v(zidx),prod(group)))
        z2=len(variables);variables.append({'name':'consecutive_pool.integrality_quotient','kind':'signed_witness'})
        R2=sub(add(mul(Es[3],Ts[4]),mul(Es[4],Ts[3])),mul(v(z2),mul(Ts[3],Ts[4])))
    else:
        R=sub(add(*(mul(mul(n,E),prod(Ts[:i]+Ts[i+1:])) for i,(n,E) in enumerate(zip(bases,Es)))),mul(v(zidx),prod(Ts)))
    # The zero-base version of the new theorem permits the unchanged
    # source bootstrap: t-block -> even F -> odd B*mu=C+F+1 -> B!=0
    # -> nonunit BH -> q=(BH)^x!=0,-1. No radix/source change is needed.
    nr=[];nl=[]
    for i,(row,lab) in enumerate(zip(rows,labels)):
        if i not in deleted:nr.append(row);nl.append(lab)
    nr.append(R);nl.append('oriented_five_base_reciprocal_pool')
    if split:
        nl[-1]='oriented_three_base_reciprocal_pool'
        nr.append(R2);nl.append('consecutive_two_base_reciprocal_pool')
    keep=[i for i in range(len(variables)) if i not in private];mp={i:j for j,i in enumerate(keep)}
    nr=[renumber(p,mp) for p in nr];variables=[variables[i] for i in keep]
    ports=[renumber(p,mp) for p in ports]
    certificate={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'private_coordinates':sorted(private),'split':split,
        'deleted_rows':sorted(deleted),'bases_parent_chart':[terms(n) for n in bases],
        'E_parent_chart':[terms(E) for E in Es],'T_parent_chart':[terms(T) for T in Ts],
        'singleton_error_identity_checks':identities,'unchanged_source_rows':True,
        'original_to_pool_chart':mp,'radical_steps':[]}
    def export(name):
        eq={'schema':'oriented-reciprocal-pool-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)',
            'variables':variables,'residuals':[{'label':lab,'terms':terms(p)} for lab,p in zip(nl,nr)],
            'scope':'Ordinary proof relative to pinned C222/Pell calibration; finite algebra checked independently.'}
        write(out/(name+'.json'),eq)
        factored={'schema':'oriented-pool-factored-v1','domain':'unrestricted integers',
          'variables':variables,'A':terms(ports[0]),'split':split,
          'quadratic_residuals':[{'label':lab,'terms':terms(p)} for lab,p in zip(nl,nr) if degree(p)<=2],
          'blocks':[{'base':terms(ports[rec['n']]),'E':terms(ports[rec['E']]),'T':terms(ports[rec['T']]),
            'requests':[dict(zip(['m','D','Y','Z'],[terms(ports[i]) for i in req])) for req in rec['requests']]} for rec in blocks],
          'pool_coordinates':[i for i,x in enumerate(variables) if x['name'] in ['oriented_pool.integrality_quotient','consecutive_pool.integrality_quotient']],
          'definitions':{'T_j':'2*A*n_j-n_j^2-1','E_j':'sum((m-D)^2-Y^2-2*n_j*Y*(m-D-Z) for each request)',
            'R_oriented':'sum(n_j*E_j*product(T_h for h!=j) for j in block_set)-z*product(T_h for h in block_set)',
            'R_consecutive':'E_3*T_4+E_4*T_3-z1*T_3*T_4','P':'sum(quadratic_residuals^2)+sum(pool_residuals^2)'},
          'oriented_block_set':list(range(3 if split else 5))}
        write(out/(name+'_factored.json'),factored)
        return {'variables':len(variables),'rows':len(nr),'degree':2*max(map(degree,nr)),
          'residual_monomials':sum(map(len,nr)),'largest_residual_monomials':max(map(len,nr)),
          'max_residual_coefficient':max(abs(a) for p in nr for a in p.values())}
    out.mkdir(parents=True,exist_ok=True)
    rawname='raw213' if split else 'raw212'
    metrics={rawname:export(rawname)}
    inherited=load(ROOT/'173-crt-index-anchor-215/stages/projection216/projection_certificate.json')
    # The five directions involve only syntax gates before coordinate 64;
    # private power deletions and all semantic changes occur after that block.
    for step in inherited['steps']:
        p=step['pivot'];d=dict(step['direction']);ri=step['deleted_row']
        must(d[p]==1,'Nonunit projection pivot')
        slopes=[dd(r,d) for r in nr]
        must(all(degree(a)<=0 for a in slopes),'Direction not in common Hessian radical')
        slope=slopes[ri].get((),0);must(slope in (-1,1),'Nonunit projection slope')
        zero=[subst(r,p,{}) for r in nr]
        restoration=scale(zero[ri],-slope)
        must(restoration==readterms(step['sheared_pivot_solution']),'Changed inherited restoration')
        newrows=[];newlabels=[]
        for i,(r,sl,lab) in enumerate(zip(zero,slopes,nl)):
            image=add(r,mul(sl,restoration))
            if i==ri:must(not image,'Pivot row did not vanish')
            else:newrows.append(image);newlabels.append(lab)
        keep=[i for i in range(len(variables)) if i!=p];mp={i:j for j,i in enumerate(keep)}
        certificate['radical_steps'].append({'pivot':p,'direction':sorted(d.items()),'deleted_row':ri,'slope':slope,
            'restoration_terms':terms(restoration),'retained_old_indices':keep})
        variables=[variables[i] for i in keep];nr=[renumber(r,mp) for r in newrows];nl=newlabels
        must(all(not dd(port,d) for port in ports),'Projection changes factored ports')
        ports=[renumber(subst(port,p,{}),mp) for port in ports]
    affine=load(ROOT/'173-crt-index-anchor-215/stages/affine215/projection_certificate.json')
    ac=affine['affine_consequence'];comb=add(*(scale(nr[i],a) for a,i in ac['row_combination']))
    must(comb==readterms(ac['affine_terms']),'Changed affine consequence')
    p=affine['eliminated_coordinate'];restore=readterms(affine['restoration_terms_original_indices'])
    must(subst(comb,p,restore)=={},'Affine restoration failure')
    omitted=affine['omitted_residual'];imgs=[subst(r,p,restore) for r in nr]
    # The certified row relation recovers the omitted row from the retained row.
    must(imgs[5]==imgs[18],'Omitted affine row not restored')
    keep=[i for i in range(len(variables)) if i!=p];mp={i:j for j,i in enumerate(keep)}
    variables=[variables[i] for i in keep];nr=[renumber(r,mp) for i,r in enumerate(imgs) if i!=omitted];nl=[lab for i,lab in enumerate(nl) if i!=omitted]
    ports=[renumber(subst(port,p,restore),mp) for port in ports]
    certificate['affine_step']={'pivot':p,'restoration_terms':terms(restore),'row_combination':ac['row_combination'],'omitted_row':omitted,'retained_old_indices':keep}
    principalname='principal207' if split else 'principal206'
    metrics[principalname]=export(principalname)
    write(out/'certificate.json',certificate);write(out/'metrics.json',metrics)
    print(json.dumps(metrics,indent=2))
    return metrics

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'oriented_pool');ap.add_argument('--split',action='store_true');a=ap.parse_args();build(a.output,a.split)
