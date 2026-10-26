#!/usr/bin/env python3
"""Compose package173's CRT anchor with package176's joint certificate."""
from pathlib import Path
import json,hashlib
from dag_parent import DAG,analyze
ROOT=Path(__file__).resolve().parents[1]
DELETED_V={144,145,146,147,148,149,204,214,215,216,217}
DELETED_R={102,103,104,105,106,107,147,153,154,155,156}

def build():
    raw=(ROOT/'source/anchor219.json').read_bytes();s=json.loads(raw)
    keep=[i for i in range(219) if i not in DELETED_V];ren={i:j for j,i in enumerate(keep)}
    d=DAG();v=lambda i:d.v(ren[i]);c=d.c
    a=lambda i,k:d.add(v(i),c(k))
    A=a(137,1);bases=[v(0),v(3),v(189),a(100,-1),v(100)]
    requests=[]
    def req(g,m,k,D,Y,Z):requests.append(dict(g=g,m=m,k=k,D=D,Y=Y,Z=Z))
    req(0,v(2),d.mul(c(1<<20),v(0)),v(186),v(187),v(188))
    req(1,v(17),v(1),v(177),v(178),a(179,1))
    req(2,a(100,-1),v(1),v(177),v(178),a(179,1))
    req(4,v(101),d.add(v(0),v(2)),v(150),v(151),v(152))
    req(3,v(102),v(0),v(141),v(142),v(143))
    req(4,v(106),a(8,-1),v(153),a(154,-1),v(155))
    for m,k,z in [(109,9,156),(112,10,159),(115,11,162),(118,12,165),
                  (122,13,171),(125,14,174),(130,15,180)]:
        req(4,v(m),v(k),v(z),v(z+1),v(z+2))
    req(3,v(119),v(4),v(168),v(169),v(170))
    req(3,v(126),v(1),v(177),v(178),a(179,1))
    req(4,v(133),d.mul(c(2),v(16)),v(183),v(184),v(185))
    T=[d.sub(d.sub(d.mul(c(2),d.mul(A,n)),d.square(n)),c(1)) for n in bases]
    E=[]
    for j,n in enumerate(bases):
        group=[r for r in requests if r['g']==j]
        H=d.sum(d.mul(r['Y'],d.sub(d.sub(r['m'],r['D']),r['Z'])) for r in group)
        S=d.sum(d.sub(d.square(d.sub(r['m'],r['D'])),d.square(r['Y'])) for r in group)
        E.append(d.sub(S,d.mul(c(2),d.mul(n,H))))
    unique=[];seen=set()
    for r in requests:
        key=(r['D'],r['Y'],r['Z'])
        if key not in seen:seen.add(key);unique.append(r)
    omega=d.sum(d.add(d.square(d.sub(d.add(r['D'],r['Z']),c(1))),d.square(d.sub(r['Y'],r['k']))) for r in unique)
    product=d.product(T);divisor=d.sub(A,c(1));z=d.v(len(keep))
    power_sum=d.sum(d.product([bases[j],E[j]]+[T[k] for k in range(5) if k!=j]) for j in range(5))
    joint=d.add(d.mul(omega,product),d.mul(divisor,d.sub(power_sum,d.mul(z,product))))
    rows=[];infos=[]
    for i,r in enumerate(s['residuals']):
        if i in DELETED_R:continue
        if any(x in DELETED_V for _,m in r['terms'] for x in m):raise ValueError(('private escape',i))
        rows.append(d.polynomial(r['terms'],ren));infos.append({'parent_row':i,'label':r['label']})
    rows.append(joint);infos.append({'parent_row':None,'label':'joint_orientation_and_power_pool'})
    root=d.sum(d.square(r) for r in rows)
    out={'schema':'conzfc.integer-polynomial-dag.v1','domain':'unrestricted integers',
         'variables':[dict(s['variables'][i],source_index=i) for i in keep]+[{'name':'joint.z','source_index':None}],
         'nodes':d.nodes,'residual_nodes':rows,'residual_info':infos,'root':root,
         'source_sha256':hashlib.sha256(raw).hexdigest(),
         'ports':{'A':A,'bases':bases,'requests':requests,'Omega':omega,'T':T,'E':E},
         'removed_variables':sorted(DELETED_V),'removed_rows':sorted(DELETED_R)}
    (ROOT/'joint209.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
    metrics=analyze(out);(ROOT/'joint209_metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics));return out
if __name__=='__main__':build()
