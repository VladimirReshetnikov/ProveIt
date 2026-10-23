#!/usr/bin/env python3
"""Exact source identities, sparse extraction certificate, and compact binding.
The checks are finite algebra. The inherited unbounded compiler is a named
mathematical dependency, not a conclusion of this program.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations_with_replacement
from math import factorial
import hashlib,json
ROOT=Path(__file__).resolve().parent

def require(ok,why):
    if not ok:raise ValueError(why)
def add(a,b,sgn=1):
    c=dict(a)
    for m,v in b.items():c[m]=c.get(m,0)+sgn*v
    return {m:v for m,v in c.items() if v}
def mul(a,b):
    c=defaultdict(int)
    for m,v in a.items():
        for n,w in b.items():c[tuple(x+y for x,y in zip(m,n))]+=v*w
    return {m:v for m,v in c.items() if v}

def source():
    s=json.loads((ROOT/'data/parent_system60.json').read_text());names=s['variables']+s['constants'];n=len(names);zero=(0,)*n
    env={v:{tuple(int(i==j) for i in range(n)):1} for j,v in enumerate(names)}
    def get(v):return {zero:v} if type(v)==int and v else {} if type(v)==int else env[v]
    for name,op,a,b in s['source']:
        a,b=get(a),get(b);env[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
    rows=[add(get(a),get(b),-1) for a,b in s['comparisons']]
    old=json.loads((ROOT/'upstream/old_parent.json').read_text());oldrows=[{tuple(t['powers']):t['coefficient'] for t in r['terms']} for r in old['equations']]
    mon=[0]*n;mon[names.index('beta')]=mon[names.index('J')]=1
    for j,(r,o) in enumerate(zip(rows,oldrows)):
        require(r==add(o,{tuple(mon):1},-1) if j==14 else r==o,'exact transport-row adjustment')
    require(len(rows)==22 and len(s['variables'])==31,'source dimensions')
    parent={k:old[k] for k in ['variables','constants','affine_abbreviations']}
    parent.update(name='compact44 source in shifted transport coordinate',domain='strictly positive integers',source_commit='beb0192cb8dc36f78c369c080f2adfbc1887a486',equations=[])
    for j,row in enumerate(rows):
        residual=old['equations'][j]['residual']
        if j==14:residual='('+residual+')-beta*J'
        parent['equations'].append({'number':j+1,'residual':residual,'terms':[{'powers':list(m),'coefficient':v} for m,v in sorted(row.items())]})
    parentraw=(json.dumps(parent,indent=2)+'\n').encode();(ROOT/'data/parent_source.json').write_bytes(parentraw)
    rows[13]=add(rows[13],rows[1]);rows[14]=add(rows[14],rows[2])
    return s,rows,hashlib.sha256(parentraw).hexdigest()

def build():
    s,rows,sourcehash=source();n=31
    code=json.loads((ROOT/'data/split_code.json').read_text());w=code['weights'];order=code['order'];qs=code['targets']
    require(len(w)==31 and len(set(w))==31 and min(w)>0,'weights')
    require(sorted(order)==list(range(1,23)) and len(qs)==22 and len(set(qs))==22,'target assignment')
    blocks=[]
    for row in rows:
        b=defaultdict(dict)
        for mon,c in row.items():
            pair=tuple(i for i,e in enumerate(mon[:n]) for _ in range(e));require(len(pair)<=2,'quadratic parent')
            fac=2 if len(pair)!=2 or pair[0]==pair[1] else 1
            b[pair][mon[n:]]=c*fac
        blocks.append(b)
    allmons={0:[()],1:[(i,) for i in range(n)],2:list(combinations_with_replacement(range(n),2))}
    grouped={d:defaultdict(list) for d in range(3)}
    for d,mm in allmons.items():
        for m in mm:grouped[d][sum(w[i] for i in m)].append(m)
    for b in blocks:
        for m in b:require(grouped[len(m)][sum(w[i] for i in m)]==[m],'same-degree label ambiguity')
    kernels=[{} for _ in range(3)];target_rows=dict(zip(qs,order));got={i:{} for i in order};checks=hits=0
    for j,q in zip(order,qs):
        for pair,c in blocks[j-1].items():
            d=len(pair);e=q-sum(w[i] for i in pair)
            require(e>=0 and e not in kernels[d],'negative/duplicate kernel exponent')
            kernels[d][e]=c
            for mm in allmons[d]:
                checks+=1;at=e+sum(w[i] for i in mm)
                if at not in target_rows:continue
                require(target_rows[at]==j and mm==pair,'foreign source term at target')
                hits+=1;fac=2 if d==2 and mm[0]!=mm[1] else 1;m=[0]*n
                for i in mm:m[i]+=1
                for p,v in c.items():
                    key=tuple(m)+p;got[j][key]=got[j].get(key,0)+fac*v
    for j in order:require(got[j]=={m:2*v for m,v in rows[j-1].items()},'literal polynomial coefficient identity')
    degrees=[max(k) for k in kernels];W=max(w);H=max(d*W+a for d,a in enumerate(degrees))
    require((W,max(qs),degrees,H)==(116,2036,[1571,1934,1836],2068),'size certificate')
    require(kernels[2][1836]=={(0,0,0,0):1},'positive leading quadratic layer')
    bits=[590069,592884,590069,590070];bounds=[]
    for kernel in kernels:
        for coeff in kernel.values():bounds.append(sum(abs(c)*(1<<sum(i*j for i,j in zip(p,bits))) for p,c in coeff.items()))
    bound=max(bounds);Cexp=(bound-1).bit_length()
    require(Cexp==1182954 and bound==1<<Cexp,'sharp coefficient majorant')
    # The maximal coefficient includes a native port, hence its actual bound is strict.
    require(all(any(any(p) for p in c) for k in kernels for c in k.values() if sum(abs(v)*(1<<sum(i*j for i,j in zip(p,bits))) for p,v in c.items())==bound),'strict port-bound maximum')
    code.update(maximum_target=max(qs),convolution_height=H,kernel_degrees=degrees,source_row_operations=[[14,2,1],[15,3,1]])
    coderaw=(json.dumps(code,indent=2)+'\n').encode();(ROOT/'data/split_code.json').write_bytes(coderaw)
    data={'variables':s['variables'],'ports':s['constants'],'source_sha256':sourcehash,'code_sha256':hashlib.sha256(coderaw).hexdigest(),'formula':'G(B,U)=D2(B)*U^2+D1(B)*U+D0(B)','kernels':[]}
    for d,kk in enumerate(kernels):data['kernels'].append({'degree':d,'terms':[{'exponent':e,'coefficient':[{'powers':list(p),'coefficient':c} for p,c in sorted(co.items())]} for e,co in sorted(kk.items())]})
    (ROOT/'data/split_kernels.json').write_text(json.dumps(data,indent=2)+'\n')
    receipt={'status':'PASS','literal_source_rows':22,'transport_adjustment':'row15_new = row15_old - beta*J','row_operations':[[14,2,1],[15,3,1]],'source_records':sum(len(k) for k in kernels),'finite_interactions':checks,'intended_contributions':hits,'target_polynomial_identities':22,'degrees':degrees,'W':W,'height':H,'maximum_target':max(qs),'coefficient_bound_exponent':Cexp,'base_scale_exponent':Cexp+12,'source_sha256':sourcehash}
    (ROOT/'certificates/SOURCE.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
    return receipt
if __name__=='__main__':build()
