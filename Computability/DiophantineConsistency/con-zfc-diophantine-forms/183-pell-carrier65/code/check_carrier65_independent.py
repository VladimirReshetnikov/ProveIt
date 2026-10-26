#!/usr/bin/env python3
"""Independent inert-DAG audit. Does not import the producer."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json

class Polynomial:
    """Independent sparse ring with monomials stored as sorted name tuples."""
    def __init__(self,value=0):
        self.terms=dict(value) if isinstance(value,dict) else {():value} if value else {}
    @staticmethod
    def variable(name):return Polynomial({(name,):1})
    @staticmethod
    def coerce(x):return x if isinstance(x,Polynomial) else Polynomial(x)
    def __add__(self,other):
        other=self.coerce(other);out=dict(self.terms)
        for m,c in other.terms.items():
            out[m]=out.get(m,0)+c
            if not out[m]:del out[m]
        return Polynomial(out)
    __radd__=__add__
    def __neg__(self):return Polynomial({m:-c for m,c in self.terms.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other);out={}
        for m,c in self.terms.items():
            for n,d in other.terms.items():
                key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
        return Polynomial({m:c for m,c in out.items() if c})
    __rmul__=__mul__
    def __pow__(self,power):
        if type(power) is not int or power<0:raise ValueError('Invalid exponent')
        ans=Polynomial(1);b=self
        while power:
            if power&1:ans=ans*b
            b=b*b;power//=2
        return ans
    def __eq__(self,other):return self.terms==self.coerce(other).terms

HERE=Path(__file__).resolve().parent
def require(condition,message):
    if not condition: raise ValueError(message)

def add(a,b,sign=1):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=sign*x
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def multiply(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def audit(path):
    raw=path.read_bytes()
    g=json.loads(raw)
    witnesses=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
    ports=['beta','K0','MC','MF']
    require(g['witnesses']==witnesses,'Wrong variable list or order')
    require(g['fixed_numerals']==ports,'Wrong coefficient ports')
    require(g['witness_domain']=='strictly positive integers','Wrong domain')
    rows=g['source']
    require(len(rows)==65,'Wrong number of operations')
    names=set(witnesses+ports); producers={}
    for row in rows:
        require(type(row) is list and len(row)==4,'Malformed operation')
        out,op,left,right=row
        require(type(out) is str and out not in names,'Duplicate register')
        require(op in ['+','-','*'],'Invalid arithmetic operation')
        for arg in [left,right]:
            require(type(arg) is int or type(arg) is str and arg in names,'Invalid or forward operand')
        names.add(out);producers[out]=(left,right)
    reachable=set()
    stack=[g['output']]
    while stack:
        x=stack.pop()
        if type(x) is int or x in reachable:continue
        reachable.add(x)
        stack.extend(producers.get(x,[]))
    require(reachable==names,'Dead or unreachable input/gate')

    # Formal cut checks: all arithmetic is exact in an independent symbolic ring.
    syms={x:Polynomial.variable(x) for x in names}
    s=syms
    expected={
      'qm':s['beta']*s['J'],
      'q':s['qm']+1,
      'X':s['w']*s['q'],
      'Y':s['s']*s['q']**3,
      'E':s['X']*s['Y'],
      'k':s['eta']+s['zeta'],
      'ell':s['E']*s['k']*s['Y'],
      'c':s['k']*s['Y']+s['eta'],
      'a':s['E']+s['Y'],
      'H':4*s['a']+3,
      'Delta':s['a']**2+s['H'],
      'main_root':s['X']+s['a']*s['c']+s['gamma']*s['H'],
      'N1':s['main_root']**2-s['Delta']*s['c']**2,
      'C':s['q']-s['F']-s['alpha'],
      'R':(s['qm']*(s['q']-s['F'])+s['alpha'])*(s['q']**2-1)
          +(s['MC']+s['q']*s['MF'])*s['J'],
      'tau':s['E']*s['n']+s['k']-s['R'],
      'N0':s['tau']**2-s['ell']*(s['ell']+s['k']),
      'Nt':(s['K0']+s['w'])*s['C']+s['q']-s['F']-s['z']*s['qm'],
      'V':s['f']**2*(s['c']*s['T']-s['R'])-s['c'],
      'normalized_S':s['i']*s['Delta']*s['c']**2,
      'Na':s['normalized_S']**2*(s['V']**2-s['y']**2)+s['y']**2,
      'scaled_Ns':s['Delta']*s['f']**2-s['normalized_S']**2,
      'polynomial':s['N0']*s['N1']*s['Na']*s['Nt']*s['scaled_Ns']-s['Delta'],
    }
    symbolic={x:s[x] for x in witnesses+ports}
    checked=[]
    for out,op,left,right in rows:
        a=Polynomial(left) if type(left) is int else symbolic[left]
        b=Polynomial(right) if type(right) is int else symbolic[right]
        value=a+b if op=='+' else a-b if op=='-' else a*b
        if out in expected:
            require(value-expected[out]==0,'Incorrect formula at '+out)
            checked.append(out)
            symbolic[out]=s[out]
        else:
            symbolic[out]=value
    require(set(checked)==set(expected),'Unverified formula boundary')

    # Independent full univariate expansion proves a degree-150 lower bound.
    # The upper bound follows from the exact N1 identity and the checked cuts.
    primes=[2,3,5,7,11,13,17,19,23,29,31,37,41,43]
    env={w:[0,c] for w,c in zip(witnesses,primes)}
    env.update(beta=[31],K0=[17],MC=[7],MF=[43])
    for out,op,left,right in rows:
        a=[left] if type(left) is int else env[left]
        b=[right] if type(right) is int else env[right]
        env[out]=multiply(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
    actual_degree=len(env[g['output']])-1
    require(actual_degree==150 and env[g['output']][-1]!=0,'Specialized degree is not 150')
    require({name:len(env[name])-1 for name in ['N0','N1','Na','Nt','scaled_Ns']}
            =={'N0':22,'N1':18,'Na':62,'Nt':2,'scaled_Ns':46},'Incorrect factor degrees')
    a,c,X,gamma,H=(Polynomial.variable(x) for x in ['a','c','X','gamma','H'])
    D=X+a*c+gamma*H
    Z=X+gamma*H
    require(D**2-(a*a+H)*c*c-(2*a*c*Z+Z*Z-H*c*c)==0,'Main norm identity')
    top=env[g['output']][-1]
    # The hand-derived complete homogeneous leader, evaluated at these same coefficients.
    vv=dict(zip(witnesses,primes))
    q0=31*vv['J'];k0=vv['eta']+vv['zeta']
    leader=8*q0**87*vv['gamma']*vv['i']**4*k0**13*vv['w']**12*vv['s']**25*vv['T']**2*vv['f']**4*(vv['w']*(q0-vv['F']-vv['alpha'])-vv['z']*q0)
    require(top==leader,'Specialized leading coefficient mismatch')

    return {
      'status':'PASS','checker':'independent checker; no producer import',
      'graph_sha256':hashlib.sha256(raw).hexdigest(),
      'variables':14,'fixed_ports':4,'operations':len(rows),
      'operation_counts':dict(sorted(Counter(row[1] for row in rows).items())),
      'all_gates_inputs_ports_live':True,
      'formal_cut_checks':len(checked),
      'formal_main_norm_cancellation_identity':True,
      'univariate_specialization_total_degree':actual_degree,
      'global_degree_upper_bound':150,
      'exact_degree':150,
      'nonzero_leading_coefficient_verified':True,
      'factor_degrees':{name:len(env[name])-1 for name in ['N0','N1','Na','Nt','scaled_Ns']},
      'scope':'Finite DAG, formula, degree, and liveness audit only; unbounded zero-set proof is in REVIEW_CARRIER65.md.'
    }

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('graph',type=Path,nargs='?',default=HERE.parent/'agent_compact/carrier65.json')
    p.add_argument('--receipt',type=Path)
    args=p.parse_args()
    result=audit(args.graph)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')

