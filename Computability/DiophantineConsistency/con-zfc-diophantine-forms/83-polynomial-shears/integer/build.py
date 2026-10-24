#!/usr/bin/env python3
"""Build five new fixed-coefficient SOS packets. Requires SymPy 1.14.

Fixed ports have weight zero in every degree calculation. Their full exact
integer bytes are distributed with this packet; no free coefficient remains.
"""
from pathlib import Path
from functools import lru_cache
import ast
import hashlib
import json
import sympy as s

ROOT = Path(__file__).resolve().parent
PORTS = ['beta','K0','MC','MF','cone_A','cone_B']
NAMES = PORTS + ['J3','F','alpha','C','z','f','h','r','v_scale','w3',
 'tau','eta','zeta','y','nu','gamma','o','j','E','c','a','V','I',
 'pair_root','pair_pos1','pair_pos2','pair_pos3']
SS = {n:s.Symbol(n) for n in NAMES}

def parse(x):
    tree=ast.parse(x,mode='eval')
    allowed=(ast.Expression,ast.BinOp,ast.UnaryOp,ast.Name,ast.Load,ast.Constant,
             ast.Add,ast.Sub,ast.Mult,ast.Pow,ast.UAdd,ast.USub)
    for node in ast.walk(tree):
        require(isinstance(node,allowed),'restricted polynomial syntax')
        if isinstance(node,ast.Name):
            require(node.id in SS,'declared symbol '+node.id)
        if isinstance(node,ast.Constant):
            require(type(node.value) is int,'integer polynomial literal')
        if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Pow):
            require(isinstance(node.right,ast.Constant) and
                    type(node.right.value) is int and node.right.value>=0,
                    'fixed nonnegative integer exponent')
    return s.sympify(x, locals=SS)

def require(p, message):
    if not p:
        raise RuntimeError(message)

def save(path, data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

def degrees_and_tops(rows, variables):
    varset={SS[x] for x in variables}
    @lru_cache(None)
    def top(e):
        if e == 0:
            return (-1,s.Integer(0))
        if not e.args:
            return (1,e) if e in varset else (0,e)
        if e.is_Add:
            ds=[top(x) for x in e.args]
            d=max(x[0] for x in ds)
            t=s.expand(sum(x[1] for x in ds if x[0]==d))
            if t != 0:
                return d,t
            # A rare cancellation of a complete leading layer. This branch
            # is needed only for small subexpressions in these five packets.
            ee=s.Poly(s.expand(e),*[SS[x] for x in variables])
            require(not ee.is_zero, 'unexpected zero retained expression')
            d=max(sum(m) for m,c in ee.terms())
            t=sum(c*s.prod(SS[x]**a for x,a in zip(variables,m))
                  for m,c in ee.terms() if sum(m)==d)
            return d,s.expand(t)
        if e.is_Mul:
            ds=[top(x) for x in e.args]
            return sum(x[0] for x in ds), s.expand(s.prod(x[1] for x in ds))
        if e.is_Pow and e.exp.is_Integer and e.exp >= 0:
            d,t=top(e.base)
            return d*int(e.exp),s.expand(t**int(e.exp))
        raise ValueError('not polynomial: '+str(e))
    return [top(r) for r in rows]

def packet(name, variables, rows, expected_degree, witness, expected_coef,
           derivation, registers=None, source=None):
    symbols=set().union(*(r.free_symbols for r in rows))
    require(symbols-set(SS[x] for x in PORTS)==set(SS[x] for x in variables),
            name+': exact declaration closure and all variables live')
    dt=degrees_and_tops(rows,variables)
    degree=2*max(d for d,t in dt)
    require(degree==expected_degree,name+': total degree')
    top_sos=s.expand(sum(t*t for d,t in dt if 2*d==degree))
    monomial=s.prod(SS[v]**a for v,a in witness.items())
    coef=s.Poly(top_sos,*[SS[x] for x in variables]).coeff_monomial(monomial)
    require(s.expand(coef-parse(expected_coef))==0,name+': actual leading certificate')
    out={'name':name,'domain':'all unrestricted integers','variables':variables,
         'variable_count':len(variables),'fixed_numerals':PORTS,
         'coefficient_binding':'../BINDING.json','residuals':[str(x) for x in rows],
         'residual_count':len(rows),'residual_degrees':[d for d,t in dt],
         'single_equation':'sum of squares of every listed residual = 0',
         'exact_degree':degree,'degree_certificate':{'monomial':witness,'coefficient':str(coef)},
         'derivation':derivation,'proof':'../PROOF.md',
         'status':'ordinary polynomial equivalence with cited source; no new kernel certificate'}
    if registers is not None:
        out['explanatory_registers']={k:str(v) for k,v in registers.items()}
    if source is not None:
        out['literal_parent']=source
        out['literal_parent_sha256']=hashlib.sha256((ROOT/source).read_bytes()).hexdigest()
    save(ROOT/'forms'/(name+'.json'),out)
    return {k:out[k] for k in ['name','variable_count','residual_count','residual_degrees','exact_degree','degree_certificate']}

def centered23():
    b=SS
    J,F,alpha,z,f,h,r,v,w,tau,eta,zeta,nu,gamma,o,j,E,a,I,t,p1,p2,p3=[b[x] for x in
       ['J3','F','alpha','z','f','h','r','v_scale','w3','tau','eta','zeta','nu','gamma','o','j','E','a','I','pair_root','pair_pos1','pair_pos2','pair_pos3']]
    beta,K0,MC,MF,A,B=[b[x] for x in PORTS]
    q=beta*(3*J+1)+1
    W=4*(3*w+1)
    X=q*W
    Y=a-E
    k=eta+zeta
    c=Y*k+eta
    V=f*o-c
    C=q-F-alpha
    H=4*a+3
    D=a*a+H
    T=E*(c-eta)
    S=X+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*(3*J+1)
    G=A*F*B*C-(q-A*F-B*C)**2
    Z=eta*zeta
    Pos=1+p1*p1+p2*p2+p3*(p3+1)
    rows=[a-E-(2*v+1)*q**3,E-X*Y,tau**2+(2*tau-k)*T-1,
          2*a*c*S+S**2-H*c*c-1,k-1-h*E-R,
          (K0+W)*C-F-z*(q-1),I-(2*r+1)*c*c,
          I*I-D*(f*f-1),(V+nu)**2-I*I*nu*(2*V+nu)-1,
          V+k-1-c*j-h*E,G*Z-(t*t-G-Z+1)**2-Pos]
    vs=['J3','F','alpha','z','f','h','r','v_scale','w3','tau','eta','zeta','nu','gamma','o','j','E','a','I','pair_root','pair_pos1','pair_pos2','pair_pos3']
    return packet('centered23_degree10',vs,rows,10,{'r':2,'a':4,'eta':4},'4',
       'From joint25_octic: replace its k0 by eta+zeta modulo its restoring row; translate tau_old=tau+E(c-eta), y_old=V+nu; eliminate c=(a-E)(eta+zeta)+eta and V=fo-c.',
       {'q':q,'W':W,'X':X,'Y':Y,'k':k,'c':c,'V':V,'C':C,'H':H,'Delta':D,'T':T,'S':S,'R':R,'G':G,'Z':Z},
       'upstream/joint__joint25_octic.json')

def pivot(parent_name,new_name,degree,witness,coef):
    rel='upstream/joint__'+parent_name+'.json'
    p=json.loads((ROOT/rel).read_text())
    q=parse('beta*(3*J3+1)+1')
    W=parse('4*(3*w3+1)')
    F=(SS['K0']+W)*SS['C']-SS['z']*(q-1)
    alpha=q-F-SS['C']
    replacements={SS['F']:F,SS['alpha']:alpha}
    rows=[parse(x).xreplace(replacements) for x in p['residuals']]
    # Locate the literal transport row without expanding other high-degree rows.
    tr=parse('(K0+4*(3*w3+1))*(beta*(3*J3+1)+1-F-alpha)-F-z*(beta*(3*J3+1))')
    hits=[i for i,x in enumerate(p['residuals']) if 'K0' in x]
    require(len(hits)==1,new_name+': unique transport row')
    idx=hits[0]
    require(s.expand(parse(p['residuals'][idx])-tr)==0,new_name+': literal transport identity')
    require(s.expand(rows[idx])==0,new_name+': deleted row zero')
    rows=[x for i,x in enumerate(rows) if i!=idx]
    variables=['C' if x=='alpha' else x for x in p['variables'] if x!='F']
    return packet(new_name,variables,rows,degree,witness,coef,
       'Invertible alpha-to-C change C=q-F-alpha, then monic transport elimination F=(K0+W)C-z(q-1); deleted parent row index '+str(idx)+'.',
       {'q':q,'W':W,'F':F,'alpha':alpha},rel)

def main():
    checks=[centered23()]
    jobs=[
      ('joint22_degree16','pivot21_degree16',16,{'a':4,'f':8,'o':4},'1'),
      ('joint21_degree20','pivot20_degree20',20,{'f':4,'v_scale':4,'J3':12},'2**4*3**12*beta**12'),
      ('joint20_degree32','pivot19_degree32',32,{'eta':4,'h':4,'w3':4,'v_scale':4,'J3':16},'2**12*3**20*beta**16'),
      ('joint19_degree88','pivot18_degree88',88,{'h':8,'w3':8,'v_scale':16,'J3':56},'2**32*3**64*beta**56')]
    for x in jobs:
        checks.append(pivot(*x))
    save(ROOT/'BUILD_CHECKS.json',{'status':'PASS','forms':checks})
    print(json.dumps(checks,indent=2))

if __name__=='__main__':
    main()
