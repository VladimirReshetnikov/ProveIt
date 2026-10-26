#!/usr/bin/env python3
"""Independent exact audit of all semantic ports in the173/176 composition.

No construction/search/projection module is imported. Only standard Python.
Run with --component-root PATH to select the final packaged component.
"""
import argparse
import hashlib
import json
from pathlib import Path
from collections import defaultdict

def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for e,c in p.items(): out[e]+=c
    return {e:c for e,c in out.items() if c}
def neg(p):return {e:-c for e,c in p.items()}
def mul(p,q):
    out=defaultdict(int)
    for e,c in p.items():
        for f,d in q.items():out[tuple(sorted(e+f))]+=c*d
    return {e:c for e,c in out.items() if c}
def C(n):return {():n} if n else {}
def V(i):return {(i,):1}
def sq(p):return mul(p,p)
def prod(ps):
    out=C(1)
    for p in ps:out=mul(out,p)
    return out
def check(test,label):
    if not test:raise ValueError(label)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--component-root',type=Path,default=Path(__file__).resolve().parents[1])
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args();root=args.component_root
    src=root/'source/anchor219.json';jp=root/'joint209.json'
    raw=src.read_bytes();s=json.loads(raw);j=json.loads(jp.read_bytes())
    check(hashlib.sha256(raw).hexdigest()=='507ffcdf7d90ef5e892c62b0e35139453de8f02ed482e9f17c14d92cbacb2cfb','frozen219 source')
    dv={144,145,146,147,148,149,204,214,215,216,217}
    dr={102,103,104,105,106,107,147,153,154,155,156}
    check(j['removed_variables']==sorted(dv) and j['removed_rows']==sorted(dr),'exact deleted interfaces')
    check([v['source_index'] for v in j['variables']]==[i for i in range(219) if i not in dv]+[None],'coordinate correspondence')
    check(len(s['variables'])==219 and len(s['residuals'])==158,'source dimensions')
    def row(i):return {tuple(e):c for c,e in s['residuals'][i]['terms']}
    for i,r in enumerate(s['residuals']):
        if i not in dr:check(not any(x in dv for _,e in r['terms'] for x in e),('private escape',i))
    check([r['parent_row'] for r in j['residual_info']]==[i for i in range(158) if i not in dr]+[None],'retained row correspondence')
    A=add(V(137),C(1));base=[V(0),V(3),V(189),add(V(100),C(-1)),V(100)]
    actual=[]
    def req(g,m,k,D,Y,Z,gate,norm):actual.append(dict(g=g,m=m,k=k,D=D,Y=Y,Z=Z,gate=gate,norm=norm))
    req(0,V(2),mul(C(1<<20),V(0)),V(186),V(187),V(188),132,133)
    req(1,V(17),V(1),V(177),V(178),add(V(179),C(1)),126,127)
    req(2,add(V(100),C(-1)),V(1),V(177),V(178),add(V(179),C(1)),126,127)
    req(4,V(101),add(V(0),V(2)),V(150),V(151),V(152),108,109)
    req(3,V(102),V(0),V(141),V(142),V(143),100,101)
    req(4,V(106),add(V(8),C(-1)),V(153),add(V(154),C(-1)),V(155),110,111)
    for m,k,z,gate in [(109,9,156,112),(112,10,159,114),(115,11,162,116),(118,12,165,118),(122,13,171,122),(125,14,174,124),(130,15,180,128)]:
        req(4,V(m),V(k),V(z),V(z+1),V(z+2),gate,gate+1)
    req(3,V(119),V(4),V(168),V(169),V(170),120,121)
    req(3,V(126),V(1),V(177),V(178),add(V(179),C(1)),126,127)
    req(4,V(133),mul(C(2),V(16)),V(183),V(184),V(185),130,131)
    vals=[];limit=j['residual_nodes'][-1]
    for ni,n in enumerate(j['nodes'][:limit+1]):
        if n[0]=='const':p=C(n[1])
        elif n[0]=='var':
            check(0<=n[1]<209,'variable range')
            original=j['variables'][n[1]]['source_index']
            p=V(219 if original is None else original)
        elif n[0] in ['add','sub','mul']:
            check(0<=n[1]<ni and 0<=n[2]<ni,'DAG dependency order')
            p={'add':add,'sub':lambda a,b:add(a,neg(b)),'mul':mul}[n[0]](vals[n[1]],vals[n[2]])
        else:raise ValueError(n)
        vals.append(p)
    ports=j['ports'];check(vals[ports['A']]==A,'actual A')
    check([vals[x] for x in ports['bases']]==base,'actual base list')
    check(len(ports['requests'])==16,'request count')
    for i,(r,p) in enumerate(zip(actual,ports['requests'])):
        check(r['g']==p['g'],('base membership',i))
        for k in ['m','k','D','Y','Z']:check(vals[p[k]]==r[k],('literal request port',i,k))
        gate=add(r['Z'],neg(mul(A,r['Y'])))
        norm=add(sq(r['D']),mul(C(2),mul(r['D'],r['Z'])),sq(r['Y']),C(-1))
        check(gate==row(r['gate']),('retained pair gate',i))
        check(norm==row(r['norm']),('retained pair norm',i))
    unique=[];seen=set()
    for r in actual:
        if r['norm'] not in seen:seen.add(r['norm']);unique.append(r)
    check(len(unique)==14,'unique pair count')
    omega=add(*(add(sq(add(r['D'],r['Z'],C(-1))),sq(add(r['Y'],neg(r['k'])))) for r in unique))
    check(vals[ports['Omega']]==omega,'actual orientation numerator')
    orientation=add(omega,neg(row(147)),neg(mul(V(137),V(204))),neg(add(*(row(r['norm']) for r in unique))))
    check(not orientation,'exact changed orientation row')
    seen=set();atoms=[]
    for p in base+[r[k] for r in actual for k in ['k','m']]:
        key=tuple(sorted(p.items()))
        if key not in seen:seen.add(key);atoms.append(p)
    frame=add(V(136),neg(row(134)))
    remainder=add(frame,neg(C(1)),neg(add(*(sq(p) for p in atoms))))
    check(remainder=={():2,(0,):2,(0,0):2},'positive frame remainder')
    Ts=[];Hs=[];Ss=[];Es=[]
    for gi,n in enumerate(base):
        group=[r for r in actual if r['g']==gi]
        T=add(mul(C(2),mul(A,n)),neg(sq(n)),C(-1))
        H=add(*(mul(r['Y'],add(r['m'],neg(r['D']),neg(r['Z']))) for r in group))
        S=add(*(add(sq(add(r['m'],neg(r['D']))),neg(sq(r['Y']))) for r in group))
        E=add(S,neg(mul(C(2),mul(n,H))))
        check(vals[ports['T'][gi]]==T,('literal denominator',gi))
        check(vals[ports['E'][gi]]==E,('literal group numerator',gi))
        Ts.append(T);Hs.append(H);Ss.append(S);Es.append(E)
        delta_sq=add(*(sq(add(r['m'],neg(r['D']),neg(mul(n,r['Y'])))) for r in group))
        pair_gates=add(*(mul(r['Y'],row(r['gate'])) for r in group))
        errid=add(delta_sq,neg(E),mul(T,add(*(sq(r['Y']) for r in group))),mul(C(2),mul(n,pair_gates)))
        check(not errid,('signed error identity modulo exact gates',gi))
    for gi,ti,qi,defrow,powrow,sgn,request in [(0,144,145,102,103,1,actual[0]),(1,146,147,104,105,1,actual[1]),(2,148,149,106,107,-1,actual[2])]:
        check(row(defrow)==mul(C(sgn),add(V(ti),neg(Ts[gi]))),('singleton modulus',gi))
        delta=add(request['m'],neg(request['D']),neg(mul(base[gi],request['Y'])))
        check(row(powrow)==add(delta,mul(V(ti),V(qi))),('singleton quotient',gi))
    for gi,ki,li,ra,rb in [(4,214,215,153,154),(3,216,217,155,156)]:
        check(row(ra)==add(V(ki),mul(add(base[gi],neg(mul(C(2),A))),V(li)),neg(mul(C(2),Hs[gi]))),('old aggregate linear',gi))
        check(row(rb)==add(Ss[gi],neg(mul(base[gi],V(ki))),V(li)),('old aggregate quadratic',gi))
    expected=add(mul(omega,prod(Ts)),mul(V(137),add(*(mul(base[i],mul(Es[i],prod([t for z,t in enumerate(Ts) if z!=i]))) for i in range(5)))),neg(mul(V(219),mul(V(137),prod(Ts)))))
    check(vals[limit]==expected,'complete new joint residual polynomial')
    degree=max(map(len,expected));check(degree==13,'exact joint residual degree13')
    out={'status':'PASS','source_sha256':hashlib.sha256(raw).hexdigest(),'joint_sha256':hashlib.sha256(jp.read_bytes()).hexdigest(),'request_count':16,'unique_pairs':14,'distinct_frame_atoms':len(atoms),'frame_remainder':[[c,list(e)] for e,c in sorted(remainder.items())],'exact_orientation_identity':True,'all_old_private_rows_bound':True,'complete_joint_residual_bound':True,'joint_residual_terms':len(expected),'joint_residual_exact_degree':degree,'joint_polynomial_exact_degree':26}
    if args.receipt:args.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
