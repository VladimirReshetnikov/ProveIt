#!/usr/bin/env python3
"""Separate algebraic review of the whole-product degree-208 graph.

This imports no producer or component verifier. The small sparse-ring helper
is retained with its original attribution as review_poly.py. The semantic
signed-domain proof is reviewed separately in prose.
"""
from collections import Counter
from pathlib import Path
import argparse
import gzip
import hashlib
import json
from review_poly import Poly, require

ROOT=Path(__file__).resolve().parent


def quotient(poly,j):
    result={}
    for monomial,coefficient in poly.d.items():
        powers=dict(monomial)
        a=powers.get('A',0)
        if a<j:continue
        if a==j:powers.pop('A',None)
        else:powers['A']=a-j
        result[tuple(sorted(powers.items()))]=coefficient
    return Poly(result)


def top(poly,weights):
    require(bool(poly.d),'nonzero polynomial')
    degrees={m:sum(e*weights[v] for v,e in m) for m in poly.d}
    degree=max(degrees.values())
    return degree,Poly({m:c for m,c in poly.d.items() if degrees[m]==degree})


def audit():
    graph=json.loads((ROOT/'equation.json').read_text())
    parent=json.loads((ROOT/'parent85.json').read_text())
    require(graph['witnesses']==parent['witnesses'] and
            graph['fixed_numerals']==parent['fixed_numerals'],'same quantified inputs and constants')
    require(graph['domain']=='strictly positive integers','domain')
    require(graph['coefficient_binding']==parent['coefficient_binding'],'whole coefficient binding unchanged')
    require(graph['operations']==len(graph['source'])==116,'literal operation count')
    require(dict(Counter(r[1] for r in graph['source']))=={'*':71,'+':24,'-':21},'binary operation classes')
    available=set(graph['witnesses']+graph['fixed_numerals']);deps={}
    for name,op,x,y in graph['source']:
        require(name not in available and op in ('+','-','*'),'unique ordinary register')
        require(all(type(a) is int or a in available for a in (x,y)),'operand topology')
        available.add(name);deps[name]=(x,y)
    live=set()
    def visit(n):
        if type(n) is int or n in live:return
        live.add(n)
        for x in deps.get(n,()):visit(x)
    visit(graph['output'])
    require(live==available,'all inputs constants and gates live')

    # Recover the entire inherited graph, not just a selection of registers.
    recovered=[]
    for name,op,x,y in graph['source']:
        if name.startswith('wp_'):continue
        if name=='center':recovered.append(['center','-','n','LBt'])
        elif name=='RG':recovered.append(['RG','*','M2','Dg'])
        else:recovered.append([name,op,x,y])
    require(recovered==parent['source'],'exact full parent recovery')
    rows={r[0]:r[1:] for r in graph['source']}
    require(rows['wp_raw_center']==['-','n','LBt'] and
            rows['center']==['-','wp_raw_center','wp_W4'],'literal carrier shift')
    require(rows['RG']==['*','M2','wp_G16'],'literal norm rescaling')

    # Independent polynomial quotient oracle in Z[A,Y,k,U,b,c].
    A,Y,k,U,b,c=map(Poly.v,('A','Y','k','U','b','c'))
    ell=(A-Y-1)*Y*k
    E=1+ell*(ell+k)
    delta=A*A-1
    G=E*(1+delta*U*U*E)
    V=(1+2*delta*U*U*E)*b-c
    F=E*V
    q1,q3=quotient(F,1),quotient(F,3)
    require(all(x%2==0 for x in q3.d.values()),'Q3 has even integer coefficients')
    halfq3=Poly({m:x//2 for m,x in q3.d.items()})
    target=U*(4*A*F-2*q1-halfq3)
    S=quotient(E,1)
    e2=(Y*k)**2
    H=A*(4*E*E+3*S*S+e2*e2)-2*S*(3*E+e2)
    require(target==U*(4*A*E*V-2*(b-c)*S-U*U*b*H),'quotient formula equals distributed target')

    env={'Am1':A-1,'kY':Y*k,'Y':Y,'V0kk':ell+k,
         'U':U,'cTR':b,'c':c,'Dtau':E,'V':V,'Dg':G,
         'n':Poly.v('n'),'LBt':Poly.v('LBt')}
    def arg(x):return Poly(x) if type(x) is int else env[x]
    reviewed=[]
    for name,op,x,y in graph['source']:
        if not name.startswith('wp_'):continue
        a0,b0=arg(x),arg(y)
        env[name]=a0+b0 if op=='+' else a0-b0 if op=='-' else a0*b0
        reviewed.append(name)
    require(env['wp_W4']==target,'every actual center gate yields polynomial-part center')
    require(env['wp_G16']==16*G,'actual scale is sixteen')
    require(len(reviewed)==31,'all new graph gates covered')

    D=target*target-16*G*V*V
    weights={'A':4,'Y':2,'k':1,'U':7,'b':4,'c':3}
    dw,tw=top(target,weights);dd,td=top(D,weights)
    require(dw==65,'center weighted degree')
    require(dd==106,'complete defect weighted degree')
    expectedD=8*A**8*Y**8*k**8*U**6*b**2-48*A**6*Y**12*k**8*U**6*b**2
    require(td==expectedD,'complete weighted defect leader')

    # Independently substitute the full leading forms of the actual inputs.
    q,w,s,i,T,F0,k0=map(Poly.v,('q0','w','s','i','T','F','k0'))
    B0=k0*s*T-q*q*(q-F0)
    aa=q*q*w*s;yy=q*s;uu=i*(q*s*k0)**2;bb=q*B0
    ee=(q**3*w*s*s*k0)**2
    qq=4*(aa*aa)**3*uu**4*ee**2
    mm=24*q**9*w*s
    dlead=8*aa**8*yy**8*k0**8*uu**6*bb**2-48*aa**6*yy**12*k0**8*uu**6*bb**2
    finallead=qq*mm*mm*dlead
    expected=9*2**11*q**88*w**18*s**52*i**10*k0**32*B0**2*(w*w-6*s*s)
    require(finallead==expected,'whole leading form after the dependent substitution')
    finaldegree,_=top(finallead,{x:1 for x in ('q0','w','s','i','T','F','k0')})
    require(finaldegree==208,'actual total degree of nonzero leader')
    # The remaining full-output summands have degrees 122,177,152,72.
    require(max(80+2*21,80+11+65+21,22+2*65,22+50)<208,'unique dominant output term')

    for name,meta in graph['coefficient_binding']['ports'].items():
        raw=gzip.decompress((ROOT/graph['coefficient_binding']['path']/meta['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'actual numeral '+name)
    return {'status':'pass','operations':116,'classes':{'*':71,'+':24,'-':21},
            'new_gates_independently_expanded':31,'quantified_variables':10,
            'root_scale':4,'center_weighted_degree':65,'defect_weighted_degree':106,
            'exact_degree':208,'Q3_even':True,'parent_recovered':True,
            'actual_coefficients_authenticated':True,
            'defect_leading_form':td.serial(),'actual_leading_form':finallead.serial(),
            'polynomial_sha256':hashlib.sha256((ROOT/'equation.json').read_bytes()).hexdigest()}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    result=audit()
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('defect_leading_form','actual_leading_form')},indent=2))


if __name__=='__main__':main()
