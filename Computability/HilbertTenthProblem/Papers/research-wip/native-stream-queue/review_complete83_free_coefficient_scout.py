#!/usr/bin/env python3
"""Independent data-only audit of the bounded free-coefficient83 scout."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

AUTHOR = {
 'complete83_free_coefficient_scout.py':'a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485',
 'complete83_free_coefficient_scout.json':'682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
 'complete83_free_coefficient_scout.md':'867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
}
PARENTS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete84_scaled_strong_output.md':'6379d0ea3e7befded4be709c1f785a0e81dd915e813608db9b0a32ffbaf9b330',
 'complete85_auxiliary_bezout_projection.md':'d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
}
S='aux_coefficient_root'
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FINAL=['norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
def require(test, message):
    if not test: raise ValueError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def graph(p):
    require(len(set(p['free']))==len(p['free']),'unique ports')
    known=set(p['free']); table={}; degree={x:0 if x in FIXED else 1 for x in known}
    for n,op,a,b in p['source']:
        require(type(n) is str and n not in known and op in ('+','-','*'),'SSA instruction')
        for x in (a,b): require(type(x) is int or type(x) is str and x in known,'operand')
        da=degree[a] if type(a) is str else 0;db=degree[b] if type(b) is str else 0
        degree[n]=da+db if op=='*' else max(da,db)
        known.add(n);table[n]=(op,a,b)
    require(p['output']==p['source'][-1][0]=='polynomial','bound full output')
    live=set();todo=[p['output']]
    while todo:
        x=todo.pop()
        if type(x) is int or x in live:continue
        live.add(x)
        if x in table:todo.extend(table[x][1:])
    require(live==known,'all rows and declared ports live')
    c=Counter(r[1] for r in p['source'])
    return dict(M=c['*'],A=c['+']+c['-'],total=len(table),free_ports=len(p['free']),witnesses=len(p['witnesses']),naive_upper=degree[p['output']])

def reconstruct(parent,p):
    old=parent['source']; row=[S,'*','i','Ac2']
    require(old.count(row)==1,'actual removed coefficient row')
    require(p['source']==[r for r in old if r!=row],'entire literal one-row deletion')
    require(p['free']==[S if n=='i' else n for n in parent['free']],'complete free interface')
    require(p['witnesses']==[S if n=='i' else n for n in parent['witnesses']],'18-coordinate replacement')
    for key in ('ordinary_input','fixed_numerals','output','factors'):
        require(p[key]==parent[key],'unchanged '+key)
    require(p['factors']==FACTORS and p['fixed_numerals']==FIXED and p['ordinary_input']=='x','concrete interface')
    require(p['witness_domain']=='strictly positive integers' and p['universal_soundness']=='UNPROVED','honest domain/scope')
    uses={v:[r[0] for r in old if v in r[2:]] for v in ['i','f','auxiliary_quotient','y_aux','Ac2']}
    require(uses==dict(i=[S],f=['L16','auxiliary_Tf'],auxiliary_quotient=['auxiliary_Tf'],y_aux=['aux_y2'],Ac2=['norm_main',S]),'all changed-coordinate consumers')
    touched={'f','auxiliary_quotient','y_aux',S}
    for n,o,a,b in p['source']:
        if a in touched or b in touched:touched.add(n)
    require(set(FACTORS)&touched=={'norm_aux','norm_strong'},'five factors unaffected by extension')
    # Rational DAG normalization: products are Laurent monomials in atomic sums.
    # This proves both full graph maps without numerical specialization.
    atoms={}; products={}
    def atom(key):
        if key not in atoms:atoms[key]=len(atoms)
        return ((atoms[key],1),)
    def multiply(a,b):
        d=Counter(dict(a));d.update(dict(b));return tuple(sorted((k,v) for k,v in d.items() if v))
    def combine(op,a,b):
        return multiply(a,b) if op=='*' else atom((op,a,b))
    def run(rows,env):
        e=dict(env)
        for n,op,a,b in rows:
            av=e[a] if type(a) is str else atom(('number',a))
            bv=e[b] if type(b) is str else atom(('number',b))
            e[n]=combine(op,av,bv)
        return e
    old_e=run(old,{n:atom(('port',n)) for n in parent['free']})
    new_e=run(p['source'],{n:old_e[S] if n==S else atom(('port',n)) for n in p['free']})
    require(all(old_e[n]==new_e[n] for n,_,_,_ in p['source']),'83 formal forward register identities')
    independent=run(p['source'],{n:atom(('independent',n)) for n in p['free']})
    inv=multiply(independent[S],tuple((k,-v) for k,v in independent['Ac2']))
    back=run(old,{n:inv if n=='i' else independent[n] for n in parent['free']})
    require(all(back[n]==independent[n] for n,_,_,_ in p['source']),'83 formal rational inverse register identities')
    return dict(consumers=uses,forward_registers=83,rational_pullback_registers=83,unchanged_factors=5,affected_factor_names=['norm_aux','norm_strong'])

# Sparse polynomials include all six compiler numeral symbols with weight zero.
# Each actual factor is expanded completely; product-finalizer nodes are separate.
class Polynomial:
    def __init__(self,variables):self.variables=variables;self.N=len(variables);self.z=(0,)*self.N
    def const(self,x):return {self.z:x} if x else {}
    def atom(self,n):
        z=list(self.z);z[self.variables.index(n)]=1;return {tuple(z):1}
    def add(self,a,b,sign=1):
        d=dict(a)
        for m,v in b.items():
            d[m]=d.get(m,0)+sign*v
            if not d[m]:del d[m]
        return d
    def mul(self,a,b):
        d={}
        for m,v in a.items():
            for n,w in b.items():
                k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+v*w
        return {k:v for k,v in d.items() if v}
    def power(self,a,n):
        r=self.const(1)
        while n:
            if n%2:r=self.mul(r,a)
            n//=2
            if n:a=self.mul(a,a)
        return r
    def top(self,a,weights):
        degrees={m:sum(i*j for i,j in zip(m,weights)) for m in a}
        d=max(degrees.values());return d,{m:c for m,c in a.items() if degrees[m]==d}
    def packed(self,a):return [[list(m),c] for m,c in sorted(a.items())]

def coefficients(p):
    P=Polynomial(p['free']);env={n:P.atom(n) for n in p['free']}
    for n,op,a,b in p['source']:
        if n in FINAL:continue
        av=env[a] if type(a) is str else P.const(a);bv=env[b] if type(b) is str else P.const(b)
        env[n]=P.mul(av,bv) if op=='*' else P.add(av,bv,1 if op=='+' else -1)
    weights=[0 if n in FIXED else 1 for n in p['free']]
    tops=[P.top(env[n],weights) for n in FACTORS]
    require([x[0] for x in tops]==[22,18,32,16,7,2,14],'independent entire factor degrees')
    Q=P.mul(env['Bm1'],env['Jrep']);k=P.add(env['eta'],env['zeta']);g=P.add(env['rho'],env['sigma'])
    C=Q
    for n in ['F','Z','alpha']:C=P.add(C,env[n],-1)
    C=P.add(C,P.mul(env['twice_cell_bits'],env['x']),-1)
    Nt=P.add(P.mul(env['w'],C),P.mul(env['transport_quotient'],Q),-1)
    wanted=P.const(-32)
    for v,e in [(Q,63),(env['h'],1),(g,1),(env['delta'],2),(k,5),(env['w'],12),(env['s'],17),(env[S],2),(Nt,1),(env['auxiliary_quotient'],2),(env['f'],4)]:wanted=P.mul(wanted,P.power(v,e))
    product=P.const(1)
    for d,top in tops:product=P.mul(product,top)
    require(product==wanted and sum(d for d,t in tops)==111,'uniform full leading form')
    exponents={'Bm1':64,'Jrep':64,'h':1,'rho':1,'delta':2,'eta':5,'w':12,'s':17,S:2,'transport_quotient':1,'auxiliary_quotient':2,'f':4}
    mon=tuple(exponents.get(n,0) for n in p['free'])
    require(product.get(mon)==32,'uniform nonzero coefficient 32*Bm1^64')
    require(P.top(env['A'],weights)[0]==12,'final subtraction cannot cancel leader')
    # Expand the actual interleaved finalizer at factor/discriminant ports.
    F=Polynomial(FACTORS+['A']);fin={n:F.atom(n) for n in FACTORS+['A']}
    for n,op,a,b in p['source']:
        if n not in FINAL:continue
        av=fin[a] if type(a) is str else F.const(a);bv=fin[b] if type(b) is str else F.const(b)
        fin[n]=F.mul(av,bv) if op=='*' else F.add(av,bv,1 if op=='+' else -1)
    expected=F.const(1)
    for n in FACTORS:expected=F.mul(expected,fin[n])
    require(fin['polynomial']==F.add(expected,fin['A'],-1),'all seven finalizer gates')
    return dict(factor_degrees=[d for d,t in tops],full_factor_terms={n:len(env[n]) for n in FACTORS},
                factor_polynomials_sha256=digest(canonical({n:P.packed(env[n]) for n in FACTORS})),
                exact_degree=111,full_leader_terms=len(product),full_leader_sha256=digest(canonical(P.packed(product))),
                uniform_coefficient='32*Bm1^64',finalizer_terms=len(expected)+1,finalizer_gates=7)

def evaluate(rows,values):
    e=dict(values)
    for n,op,a,b in rows:
        x=e[a] if type(a) is str else a;y=e[b] if type(b) is str else b
        e[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return e

def numerical(parent,p):
    values_checked=0
    for j in range(36):
        values={n:Fraction(((j+11)*(k+5))%37-18,1 if j<18 else 2+k%5) for k,n in enumerate(parent['free'])}
        a=evaluate(parent['source'],values)
        b=evaluate(p['source'],{n:a[S] if n==S else values[n] for n in p['free']})
        require(all(a[n]==b[n] for n,_,_,_ in p['source']),'complete signed forward sample');values_checked+=83
    for j in range(30):
        values={n:Fraction(2+(j+7)*(k+3)%19,1+k%4) for k,n in enumerate(p['free'])}
        b=evaluate(p['source'],values);require(b['Ac2']>0,'positive rational denominator')
        a=evaluate(parent['source'],{n:values[S]/b['Ac2'] if n=='i' else values[n] for n in parent['free']})
        require(all(a[n]==b[n] for n,_,_,_ in p['source']),'complete rational pullback sample');values_checked+=83
    return dict(forward=36,rational_forward=18,rational_inverse=30,retained_values=values_checked)

# Independent 2x2 matrix recurrence, and quotient residues from chi modulo S*m.
# No division by a nonunit in a residue ring and no ancestor helper is used.
def pell(A,n,mod=None):
    require(A>=2 and n>=0,'Pell input')
    def mm(x,y):
        z=tuple(sum(x[2*i+k]*y[2*k+j] for k in range(2)) for i in range(2) for j in range(2))
        return tuple(t%mod for t in z) if mod else z
    R=(1,0,0,1);M=(A,A*A-1,1,A)
    while n:
        if n%2:R=mm(R,M)
        n//=2
        if n:M=mm(M,M)
    return R[0],R[2]

def quotient_residue(S,t,m):
    chi,_=pell(S,t,S*m)
    require(chi%S==0,'integer quotient residue')
    return (chi//S)%m

def component(A,p,materialize):
    Delta=A*A-1;D,c=pell(A,p)
    require(p>1 and p%2==1 and c>2 and c%2==1 and math.gcd(c,D)==1,'main fixture hypotheses')
    if p%4==3:f,v,t=D,c,p
    else:
        f,v=pell(A,2*p)
        # Search the short arithmetic progression of residues modulo 8p;
        # independent of the author modular-inverse CRT implementation.
        candidates=[p+c*j for j in range(8*p) if (p+c*j)%(8*p)==3*p%(8*p)]
        require(candidates,'compatible CRT');t=min(candidates)
        require(v==2*D*c,'actual duplicate main ordinate')
        require(pell(A,4*p,f)==(f-1,0) and pell(A,8*p,f)==(1,0),'half-index signs')
        require(pell(A,t,f)[1]==c%f,'transport of auxiliary index')
        require(pell(A,3*p)[1]==(2*f+1)*c,'exact triplication')
    Scoef=Delta*v
    require(t%4==3 and t%c==p%c,'negative odd-quotient sign and target residue')
    require(Delta*f*f-Scoef*Scoef==Delta,'scaled strong factor')
    require(quotient_residue(Scoef,t,c)==(-p)%c and quotient_residue(Scoef,t,f)==(-c)%f,'two quotient residues')
    require(math.gcd(c,f)==1 and f*f%c==1,'coprime denominator split')
    inverse=Fraction(Scoef,Delta*c*c)
    require(inverse.denominator>1 and inverse==Fraction(1 if p%4==3 else 2*D,c),'noninteger literal inverse')
    r=dict(A=A,p=p,auxiliary_index=t,branch=p%4,c_bits=c.bit_length(),inverse=[inverse.numerator,inverse.denominator],materialized=materialize)
    if materialize:
        chi,y=pell(Scoef,t);require(chi%Scoef==0,'odd chi divisibility');V=chi//Scoef
        num=V+c+p*f*f;require(num%(c*f)==0,'positive integer Bezout witness');T=num//(c*f)
        require(min(T,V,y,f,Scoef)>0,'positive component coordinates')
        require(c*(T*f-1)-p*f*f==V,'literal V reconstruction')
        require(Scoef*Scoef*(V*V-y*y)+y*y==1,'entire auxiliary factor')
        require((Delta*f*f-Scoef*Scoef)*(Scoef*Scoef*(V*V-y*y)+y*y)-Delta==0,'full output conditional on five unit factors')
        r.update(V_bits=V.bit_length(),y_bits=y.bit_length(),T_bits=T.bit_length(),component_sha256=digest(canonical([hex(x) for x in [f,Scoef,V,y,T]])))
    return r

def polynomial_pell_identities():
    P=Polynomial(['A']);A=P.atom('A');one=P.const(1);Z=P.add(one,P.mul(A,A),-1)
    psi=[{},one]
    for n in range(42):psi.append(P.add(P.mul(P.mul(P.const(2),A),psi[-1]),psi[-2],-1))
    q0=one;q1=P.add(P.mul(P.const(4),Z),P.const(3),-1)
    count=0
    for h in range(21):
        q=q0 if h==0 else q1
        require(q=={m:(-1)**h*c for m,c in psi[2*h+1].items()},'full odd polynomial identity')
        require(q.get(P.z,0)==1,'Q_h(1) exact constant')
        count+=1
        if h:
            q0,q1=q1,P.add(P.mul(P.add(P.mul(P.const(4),Z),P.const(2),-1),q1),q0,-1)
    # Independently evaluate Q_h(0) via the scalar recurrence for all h.
    a,b=1,-3
    for h in range(41):
        q=a if h==0 else b
        require(q==(-1)**h*(2*h+1),'Q_h(0) exact')
        if h:a,b=b,-2*b-a
    return dict(odd_polynomial_identities=count,zero_argument_identities=41)

def verify(root,author_root):
    for n,pin in PARENTS.items():require(digest((root/n).read_bytes())==pin,'parent pin '+n)
    for n,pin in AUTHOR.items():require(digest((author_root/n).read_bytes())==pin,'author pin '+n)
    receipt=json.loads((author_root/'complete83_free_coefficient_scout.json').read_text())
    require(receipt['dependency_pins']==PARENTS,'exact announced dependency pins')
    require(receipt['source_sha256']==AUTHOR['complete83_free_coefficient_scout.py'],'receipt binds author source')
    p=receipt['packet'];parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
    gd=reconstruct(parent,p);oldledger=graph(parent);ledger=graph(p)
    require(oldledger['total']==84 and ledger==dict(M=46,A=37,total=83,free_ports=25,witnesses=18,naive_upper=121),'independent paid ledger')
    claimed=dict(M=46,A=37,total=83,core_M=40,core_A=36,core_total=76,finalizer_M=6,finalizer_A=1,finalizer_total=7)
    require(p['ledger']==claimed and p['factor_exact_degrees']==[22,18,32,16,7,2,14] and p['exact_degree']==111,'saved metadata agrees')
    degree=coefficients(p)
    cases=[component(A,p,(A,p) in [(2,3),(3,7),(2,5),(6,27)]) for A,p in [(2,3),(3,7),(4,11),(9,15),(2,5),(3,5),(5,9),(11,13),(7,17),(13,21),(6,27),(8,29)]]
    return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PARENTS,
                full_source_sha256=digest(canonical(p['source'])),ledger=ledger,graph=gd,degree=degree,
                numerical=numerical(parent,p),pell_polynomial_checks=polynomial_pell_identities(),component_cases=cases,
                proof_scope='Both full-positive-zero extension branches reviewed; finite Pell fixtures are components, not full compiler zeros. No universal83 or false-input theorem.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--author-root',type=Path)
    ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
    require(not(a.output and a.expect),'choose writer or replay')
    r=verify(a.root,a.author_root or a.root)
    require(exact(r,json.loads(json.dumps(r))),'type-exact JSON round trip')
    if a.expect:require(exact(r,json.loads(a.expect.read_text())),'exact saved receipt mismatch')
    if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',gates=83,degree=111,factor_terms=sum(r['degree']['full_factor_terms'].values()),pell_cases=len(r['component_cases']),universal_soundness='UNPROVED')))
if __name__=='__main__':main()
