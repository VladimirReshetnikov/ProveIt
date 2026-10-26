#!/usr/bin/env python3
"""Build and independently audit the first-Pell carrier, standard library only.

The parent JSON is inert data pinned to ProveIt commit
02a78a08603cbae248c19c23a75907c6c6bd6443.
The finite checks do not prove consistency or replace the ordinary proof.
"""
from pathlib import Path
from collections import Counter
import hashlib, json, random

HERE=Path(__file__).resolve().parents[1]
def need(ok,msg):
    if not ok: raise ValueError(msg)

def make_child(parent):
    rows=[]
    first={name:row for row in parent['source'] for name in [row[0]]
           if name in ('tau2','ell_plus_k','first_product','N0')}
    remove=set(first)|{'hE','index_partial','Nk','product2'}
    for row in parent['source']:
        name,op,left,right=row
        if name in remove: continue
        if name=='product3': left='product1'
        rows.append([name,op,left,right])
        if name=='R':
            rows.extend([['En','*','E','n'],['tau_partial','+','En','k'],
                         ['tau','-','tau_partial','R']])
            rows.extend(first[key] for key in ('tau2','ell_plus_k','first_product','N0'))
    out={key:parent[key] for key in ('fixed_numerals','coefficient_binding','witness_domain')}
    out.update(schema='literal_integer_arithmetic_dag_v1',
        name='admissible942_first_pell_carrier65_degree150',
        source=rows,output='polynomial',
        witnesses=[('n' if v=='tau' else v) for v in parent['witnesses'] if v!='h'],
        operations=len(rows),operation_counts=dict(Counter(r[1] for r in rows)),
        exact_degree=150,
        parent_sha256=hashlib.sha256((HERE/'sources/parent_polynomial.json').read_bytes()).hexdigest(),
        proof='CARRIER65_PROOF.md',
        proof_boundary='New exact positive-zero bijection composed with pinned admissible942 P66 calibration; no new end-to-end formal-kernel replay.')
    out['coefficient_binding']={'schema':'four_fixed_positive_integers_v1','directory':'coefficients','manifest':'coefficients.json','ports':{'beta':'beta.bin','K0':'K.bin','MC':'MC.bin','MF':'MF_source.bin'},'encoding':'minimal unsigned big-endian','source_commit':'02a78a08603cbae248c19c23a75907c6c6bd6443'}
    out['proof']='../proofs/CARRIER65_PROOF.md'
    out['proof_boundary']='Explicit positive-zero maps and zero-existence equivalence composed with the pinned admissible942 P66 calibration; no new end-to-end formal-kernel replay.'
    return out

def evaluate(graph,inputs):
    env=dict(inputs)
    for name,op,left,right in graph['source']:
        a=left if isinstance(left,int) else env[left]
        b=right if isinstance(right,int) else env[right]
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env

def scalar_formula(v):
    J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma=(v[k] for k in
        ['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'])
    q=v['beta']*J+1; C=q-F-alpha; X=w*q; Y=s*q**3
    E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H
    ell=E*k*Y;D=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(v['MC']+q*v['MF'])*J
    tau=E*n+k-R;V=f*f*(c*T-R)-c;S=i*Delta*c*c
    N0=tau*tau-ell*(ell+k);N1=D*D-Delta*c*c
    Na=S*S*(V*V-y*y)+y*y;Nt=(v['K0']+w)*C+q-F-z*(q-1)
    Ns=Delta*f*f-S*S
    return N0*N1*Na*Nt*Ns-Delta

# Sparse integer polynomial arithmetic. Treat all four coefficient ports as
# symbolic degree-zero coordinates, and all witnesses as degree-one coordinates.
def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if out[m]==0: del out[m]
    return out
def mul(a,b):
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(x+y for x,y in zip(ma,mb))
            out[m]=out.get(m,0)+ca*cb
    return {m:c for m,c in out.items() if c}
def top(poly,weights):
    if not poly:return (-1,{})
    degree=max(sum(x*w for x,w in zip(m,weights)) for m in poly)
    return degree,{m:c for m,c in poly.items() if sum(x*w for x,w in zip(m,weights))==degree}

def certify_degree(graph):
    names=graph['witnesses']+graph['fixed_numerals'];n=len(names)
    weights=[1]*len(graph['witnesses'])+[0]*len(graph['fixed_numerals'])
    zero=(0,)*n
    def const(x):return {zero:x} if x else {}
    env={}
    for j,name in enumerate(names):
        m=[0]*n;m[j]=1;env[name]=(weights[j],{tuple(m):1})
    def get(x):return (0,const(x)) if isinstance(x,int) else env[x]
    # The only cancelling leading cut is N1. Expand its entire ancestor cone
    # exactly, independently of degree heuristics.
    rows={r[0]:r for r in graph['source']}
    full={name:p for name,(_,p) in env.items()}
    def expand(x):
        if isinstance(x,int):return const(x)
        if x in full:return full[x]
        _,op,l,r=rows[x];a=expand(l);b=expand(r)
        out=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        full[x]=out;return out
    exact_main=expand('N1')
    record={}
    for name,op,l,r in graph['source']:
        da,pa=get(l);db,pb=get(r)
        if name=='N1':env[name]=top(exact_main,weights)
        elif op=='*':env[name]=(da+db,mul(pa,pb))
        else:
            highest=max(da,db)
            out=add(pa if da==highest else {},pb if db==highest else {},1 if op=='+' else -1)
            need(bool(out),'Unexpected leading cancellation at '+name)
            env[name]=(highest,out)
        record[name]=env[name][0]
    # Independently assemble the proposed full degree-150 leading form.
    def p(name):return full[name]
    def power(poly,k):
        out=const(1)
        for _ in range(k):out=mul(out,poly)
        return out
    q0=mul(p('beta'),p('J'));k0=add(p('eta'),p('zeta'))
    expected=const(8)
    for poly,k in [(q0,87),(p('gamma'),1),(p('i'),4),(k0,13),
                   (p('w'),12),(p('s'),25),(p('T'),2),(p('f'),4)]:
        expected=mul(expected,power(poly,k))
    transport=add(mul(p('w'),add(add(q0,p('F'),-1),p('alpha'),-1)),mul(p('z'),q0),-1)
    expected=mul(expected,transport)
    need(env['polynomial']==(150,expected),'Full degree-150 leading form mismatch')
    mon=[0]*n
    for name,power_ in {'J':88,'gamma':1,'i':4,'eta':13,'w':12,'s':25,'T':2,'f':4,'z':1,'beta':88}.items():mon[names.index(name)]=power_
    need(expected.get(tuple(mon))==-8,'Selected nonzero coefficient is not -8*beta^88')
    return {'factor_degrees':{k:record[k] for k in ['N0','N1','Na','Nt','scaled_Ns']},
            'exact_degree':record['polynomial'],'leading_terms':len(expected),
            'full_main_norm_terms':len(exact_main),
            'nonzero_selected_coefficient':'-8*beta^88',
            'leading_form':'8*(beta*J)^87*gamma*i^4*(eta+zeta)^13*w^12*s^25*T^2*f^4*(w*(beta*J-F-alpha)-z*beta*J)'}

def audit(graph,parent):
    need(len(graph['witnesses'])==14,'Witness count')
    need(len(graph['source'])==65,'Operation count')
    known=set(graph['witnesses'])|set(graph['fixed_numerals'])
    producers={}
    for row in graph['source']:
        name,op,a,b=row
        need(op in ('+','-','*'),'Unknown operation')
        need(name not in known,'Duplicate definition')
        for operand in [a,b]:need(isinstance(operand,int) or operand in known,'Forward reference')
        known.add(name);producers[name]=[a,b]
    live=set()
    def visit(x):
        if isinstance(x,int) or x in live:return
        live.add(x)
        for y in producers.get(x,[]):visit(y)
    visit(graph['output']);need(live==known,'Dead input or gate')
    rng=random.Random(20261025)
    for case in range(128):
        v={key:rng.randint(-5,9) for key in graph['witnesses']+graph['fixed_numerals']}
        got=evaluate(graph,v)
        need(got['polynomial']==scalar_formula(v),'Independent formula mismatch')
        # All-ring identity at the formal substitution h=(k-R-1)/E is
        # equivalently the cut Pparent = (Nk)*(Pchild+Delta)-Delta.
        old=dict(v);old['h']=rng.randint(-6,7);old['tau']=got['tau']
        oldenv=evaluate(parent,old)
        need(oldenv['polynomial']==oldenv['Nk']*(got['polynomial']+got['Delta'])-got['Delta'],'Full-product substitution identity')
    # Exact Pell-family quotient map, including indices one and zero exclusions.
    pell_checks=0
    for E in range(2,13):
        for Y in range(1,7):
            p=2*E*Y+1;x,u=1,0
            for rank in range(1,7):
                x,u=p*x+(p*p-1)*u,x+p*u
                k=2*u
                need(x*x-E*Y*(E*Y+1)*k*k==1,'First Pell family')
                need((x-1)%E==0,'Pell root congruence')
                need(x>k,'Pell root strict bound')
                for R in range(2,E-1):
                    if (k-R-1)%E:continue
                    h=(k-R-1)//E;n=(x-k+R)//E
                    need(h>0 and n>0 and E*n+k-R==x,'Exact carrier inverse')
                    pell_checks+=1
    return {'status':'PASS','variables':14,'operations':65,
            'operation_counts':graph['operation_counts'],'all_nodes_and_ports_live':True,
            'signed_full_formula_diagnostics':128,'pell_carrier_diagnostics':pell_checks,
            **certify_degree(graph)}

