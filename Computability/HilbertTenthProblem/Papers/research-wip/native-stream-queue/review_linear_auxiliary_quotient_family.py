#!/usr/bin/env python3
"""Independent full-factor audit of the four linear-input quotient sources."""
import argparse, hashlib, json
from collections import Counter
from functools import reduce
from pathlib import Path

FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(data):return hashlib.sha256(data).hexdigest()
def pconst(c):return {():c} if c else {}
def atom(name):return {(name,):1}
def add(a,b,sign=1):
    c=a.copy()
    for m,v in b.items():
        c[m]=c.get(m,0)+sign*v
        if not c[m]:del c[m]
    return c
def mul(a,b):
    c=Counter()
    for m,v in a.items():
        for n,w in b.items():c[tuple(sorted(m+n))]+=v*w
    return {m:v for m,v in c.items()if v}
def square(a):return mul(a,a)
def degree(p):return max((sum(v not in FIXED for v in m) for m in p),default=-1)
def leader(p):
    d=degree(p)
    return {m:v for m,v in p.items()if sum(x not in FIXED for x in m)==d}
def phash(p):return digest(json.dumps([[list(m),v]for m,v in sorted(p.items())],separators=(',',':')).encode())
def scan(rows,ports,output):
    known=set(ports);by={};M=A=0
    need(len(ports)==len(known),'unique ports')
    for name,op,a,b in rows:
        need(type(name)is str and name not in known and op in ['+','-','*'],'register syntax')
        for v in [a,b]:need(type(v)is int or(type(v)is str and v in known),'topological references')
        by[name]=(op,a,b);known.add(name);M+=op=='*';A+=op!='*'
    live=set()
    def walk(v):
        if type(v)is int or v in live:return
        live.add(v)
        if v in by:
            _,a,b=by[v];walk(a);walk(b)
    walk(output)
    need(known==live,'all rows and all ports live')
    return {'M':M,'A':A,'operations':M+A,'witnesses':len(ports)-len(FIXED)-1}

def direct_formulas(ports,first_gap,aux_gap):
    z={name:atom(name)for name in ports};cst=pconst
    plus=lambda *ps:reduce(add,ps,{})
    q=add(mul(z['Bm1'],z['Jrep']),cst(1));q2=square(q);q3=mul(q2,q)
    X=mul(z['w'],q);Y=mul(z['s'],q3);E=mul(X,Y)
    k=add(z['eta'],z['zeta']);c=add(mul(k,Y),z['eta']);a=add(E,Y)
    H=add(mul(cst(4),a),cst(3));Delta=add(square(a),H)
    D=plus(X,mul(a,c),mul(add(z['rho'],z['sigma']),H))
    U=add(q,z['F'],-1);QFZ=add(U,z['Z'],-1)
    C=add(add(QFZ,z['alpha'],-1),mul(z['twice_cell_bits'],z['x']),-1)
    W=add(C,z['Z'],-1);input_index=plus(mul(z['twice_cell_bits'],z['x']),z['inner_bits'],mul(z['delta'],add(a,cst(1))))
    mu=plus(W,mul(a,input_index),mul(z['rho'],H))
    G=add(mul(add(q,cst(1),-1),U),QFZ)
    R=plus(mul(G,add(q2,cst(1),-1)),mul(add(z['MC'],mul(q,z['MF'])),z['Jrep']))
    f2=square(z['f']);Kaux=mul(Delta,add(f2,cst(1),-1))
    V=add(mul(c,add(mul(z['auxiliary_quotient'],z['f']),cst(1),-1)),mul(R,f2),-1)
    y=add(V,z['aux_gap'])if aux_gap else z['y_aux']
    L=mul(E,mul(k,Y))
    Nfirst=add(square(z['tau_gap']),mul(L,add(mul(cst(2),z['tau_gap']),k,-1))) if first_gap else add(square(z['tau_root']),mul(L,add(L,k)),-1)
    out=[Nfirst,add(square(D),mul(Delta,square(c)),-1),add(square(mu),mul(Delta,square(input_index)),-1),add(mul(Kaux,add(square(V),square(y),-1)),square(y)),add(add(k,mul(z['h'],E),-1),R,-1),add(add(mul(add(z['Kconstant'],z['w']),C),U),mul(z['transport_quotient'],add(q,cst(1),-1)),-1),add(add(square(mul(z['i'],square(c))),Kaux,-1),cst(1))]
    return dict(zip(FACTORS,out))

def power(p,n):
    out=pconst(1)
    for _ in range(n):out=mul(out,p)
    return out

def expected_leaders(ports,first_gap,aux_gap):
    z={n:atom(n)for n in ports};Q=mul(z['Bm1'],z['Jrep']);k=add(z['eta'],z['zeta'])
    gamma=add(z['rho'],z['sigma'])
    def product(coef,*pairs):
        return reduce(mul,[power(p,e)for p,e in pairs],pconst(coef))
    first=product(1,(z['w'],1),(k,1),(z['s'],2),(Q,7),(add(mul(pconst(2),z['tau_gap']),k,-1),1))if first_gap else product(-1,(z['w'],2),(k,2),(z['s'],4),(Q,14))
    main=product(8,(gamma,1),(z['w'],2),(k,1),(z['s'],3),(Q,11))
    inp=product(4,(z['delta'],1),(add(mul(pconst(2),z['rho']),z['delta'],-1),1),(z['w'],3),(z['s'],3),(Q,12))
    aux=product(-2,(z['w'],2),(k,1),(z['s'],3),(Q,11),(z['auxiliary_quotient'],1),(z['f'],3),(z['aux_gap'],1))if aux_gap else product(1,(z['w'],2),(k,2),(z['s'],4),(Q,14),(z['auxiliary_quotient'],2),(z['f'],4))
    index=product(-1,(z['h'],1),(z['w'],1),(z['s'],1),(Q,4))
    C=add(add(add(add(Q,z['F'],-1),z['Z'],-1),z['alpha'],-1),mul(z['twice_cell_bits'],z['x']),-1)
    transport=add(mul(z['w'],C),mul(z['transport_quotient'],Q),-1)
    strong=product(1,(z['i'],2),(k,4),(z['s'],4),(Q,12))
    return dict(zip(FACTORS,[first,main,inp,aux,index,transport,strong]))

def cone(rows,outputs,cuts=()):
    by={r[0]:r for r in rows};wanted=set();cuts=set(cuts)
    def visit(v):
        if type(v)is int or v in wanted or v in cuts:return
        wanted.add(v)
        if v in by:
            _,_,l,r=by[v];visit(l);visit(r)
    for n in outputs:visit(n)
    return [r for r in rows if r[0]in wanted]

def poly_run(rows,initial):
    e=initial.copy()
    for name,op,l,r in rows:
        need(name not in e,'poly register freshness')
        a=pconst(l)if type(l)is int else e[l]
        b=pconst(r)if type(r)is int else e[r]
        e[name]=mul(a,b)if op=='*'else add(a,b,1 if op=='+'else -1)
    return e

def abstract_finalizer(rows,output,factors):
    e=poly_run(cone(rows,[output],factors),{n:atom(n)for n in factors})
    need(e[output]==add(reduce(mul,[atom(n)for n in factors],pconst(1)),pconst(1),-1),'complete factor product-minus-one')
    return phash(e[output])

def independent_factor_audit(rows,ports,output,first_gap,aux_gap):
    ledger=scan(rows,ports,output)
    e=poly_run(cone(rows,FACTORS),{n:atom(n)for n in ports})
    formulas=direct_formulas(ports,first_gap,aux_gap)
    expected=expected_leaders(ports,first_gap,aux_gap)
    for n in FACTORS:
        need(e[n]==formulas[n],'whole factor '+n)
        need(leader(e[n])==expected[n],'uniform leader '+n)
    whole=reduce(mul,[leader(e[n])for n in FACTORS],pconst(1))
    final=abstract_finalizer(rows,output,FACTORS)
    return dict(ledger=ledger,factors=[dict(name=n,terms=len(e[n]),degree=degree(e[n]),whole_coefficient_sha256=phash(e[n]),leading_terms=len(leader(e[n])),leading_coefficient_sha256=phash(leader(e[n])))for n in FACTORS],exact_degree=degree(whole),whole_leading_terms=len(whole),whole_leading_coefficient_sha256=phash(whole),finalizer_sha256=final),e

def parent_correction_audit(parent_rows,child_polys,child_ports):
    c=child_polys['R10a'];R=child_polys['r_lhs'];f=atom('f');T=atom('auxiliary_quotient')
    o=add(mul(c,T),mul(R,f),-1)
    j=atom('independent_j')
    inputs={n:atom(n)for n in child_ports};inputs['o']=o;inputs['j']=j
    # The parent has neither new supplied quotient nor dependencies on it;
    # those symbols occur only in the exact polynomial restoration of o.
    old=poly_run(cone(parent_rows,FACTORS+['norm_linear']),inputs)
    for n in FACTORS:need(old[n]==child_polys[n],'retained parent whole factor '+n)
    correction=add(add(child_polys['norm_index'],child_polys['aux_u_rhs']),R)
    correction=add(correction,mul(c,j),-1)
    need(old['norm_linear']==correction,'whole polynomial omitted-factor correction')
    return dict(retained_whole_factors=len(FACTORS),omitted_factor_terms=len(correction),omitted_factor_sha256=phash(correction),identity='Fparent(o=cT-Rf,j)+1=(Fchild+1)*(Nk+V+R-cj)',domain='Every commutative ring; j remains independent. Rational pullback j=(V+R)/c additionally requires c nonzero.')

def same(a,b):
    if type(a)is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
    if isinstance(a,list):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
    return a==b

PINS = {'complete_linear_auxiliary_quotient_family.py': '07d9bd66528a213929475ab560a0265fa872c88599d9b9700fdc5d4910a31153', 'complete_linear_auxiliary_quotient_family.json': 'b2cb2723c3a335df84b8f3472371912beb28cc52b0f07d0b68d4d0d0fcb6a2b5', 'complete_linear_auxiliary_quotient_family.md': '7e85f2e3a236872da22be9d85222289475ebfb825b733e3e881c5a2b220eed66', 'transport_shear_partition_census.json': '93becb442a3809f855053f414e8478e92b2b5eed0ff84c1cb22996b9a0ac1ef0', 'transport_shear_partition_census.md': '27f38b0757d220e605565c6d63ff3470a73292a9cb632a8c529e8d1b89804469', 'review_transport_shear_partition_census.md': '011b3d5c8463014ec7449a3a7aad8155906f2f1303538ab0fed02660f1332de2', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570', 'complete75_linear_input_modulus89.md': '855a1e038dac816043c040decd35d33818e0da25e1e9e1713a9a454bcc531444', 'complete75_auxiliary_gap_degree_tradeoffs.md': '315792b00530a4517e7f79f3c423f860268145803eb9bc364a235782aad69755'}
CASES=[('root_ordinate',3,False,False,87,119),('root_gap',8,False,True,88,113),('gap_ordinate',16,True,False,88,109),('gap_gap',21,True,True,89,103)]

def verify(root):
    need(bool(PINS),'final source pins required')
    for name,pin in PINS.items():need(digest((root/name).read_bytes())==pin,'authenticated '+name)
    author=json.loads((root/'complete_linear_auxiliary_quotient_family.json').read_text())
    for name,pin in author['parent_pins'].items():need(digest((root/name).read_bytes())==pin,'author dependency '+name)
    old=json.loads((root/'transport_shear_partition_census.json').read_text())
    bymode={f['mode']:f for f in author['forms']}
    need(len(bymode)==len(author['forms'])==4,'exact four-source scope')
    forms=[]
    for mode,index,fg,ag,ops,deg in CASES:
        item=bymode[mode];p=item['packet']
        need(item['parent_form_index']==index and p['first_gap']is fg and p['auxiliary_gap']is ag,'parent/coordinate identity')
        parent=old['forms'][index]
        winners=[w for w in parent['winners']if len(w['partition'])==1 and w['anchor']==0]
        need(len(winners)==1,'actual full product parent selected')
        parent_packet=winners[0]
        expected_ports=[('auxiliary_quotient'if n=='j'else n)for n in parent['witnesses']if n!='o']+['x']+FIXED
        need(p['free']==expected_ports and p['fixed_numerals']==FIXED and p['ordinary_input']=='x','entire fixed/free interface')
        need(p['witnesses']==expected_ports[:-7] and p['factors']==FACTORS,'eighteen positive witnesses and seven factors')
        audit,polys=independent_factor_audit(p['source'],p['free'],p['output'],fg,ag)
        need(audit['ledger']['operations']==ops and audit['ledger']['witnesses']==18 and audit['exact_degree']==deg,'full exact resources')
        need(p['exact_degree']==deg and p['ledger']['operations']==ops and p['ledger']['M']==audit['ledger']['M'] and p['ledger']['A']==audit['ledger']['A'],'author resource agreement')
        audit['parent_finalizer_sha256']=abstract_finalizer(parent_packet['source'],parent_packet['output'],FACTORS+['norm_linear'])
        audit['parent_correction']=parent_correction_audit(parent_packet['source'],polys,p['free'])
        audit['mode']=mode;audit['parent_form_index']=index
        forms.append(audit)
    return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'pins':PINS.copy(),'forms':forms,'totals':{'complete_sources':4,'paid_gates':sum(f['ledger']['operations']for f in forms),'factor_coefficient_terms':sum(sum(p['terms']for p in f['factors'])for f in forms),'whole_leading_terms':sum(f['whole_leading_terms']for f in forms),'positive_witnesses_each':18},'scope':'Four complete 18-witness linear-input sources and their actual historical product parents. Whole integer-coefficient factor expansions, paid live sources, complete finalizers and all-value ring corrections checked independently without running parent Python. Infinite-domain positivity and uniform fixed-program soundness are proved in the accompanying review; no complete universal Pell witness is materialized.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--expect',type=Path);ap.add_argument('--output',type=Path);args=ap.parse_args()
    result=verify(args.root)
    need(same(result,json.loads(json.dumps(result))),'exact typed JSON roundtrip')
    if args.expect:need(same(result,json.loads(args.expect.read_text())),'exact receipt replay')
    if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'totals':result['totals'],'forms':[{'mode':x['mode'],'operations':x['ledger']['operations'],'exact_degree':x['exact_degree']}for x in result['forms']]},sort_keys=True))

if __name__=='__main__':main()
