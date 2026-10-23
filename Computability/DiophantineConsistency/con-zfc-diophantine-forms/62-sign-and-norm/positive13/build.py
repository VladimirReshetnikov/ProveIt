#!/usr/bin/env python3
"""Literal 13-positive root-centered norm; all fixed-scalar gates charged."""
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
VARIABLES = ['J','F','alpha','z','f','i','T','s','w','eta','zeta','gamma','t']
PORTS = ['beta','K0','MC','MF']


def require(condition,message):
    if not condition:
        raise ValueError(message)


class Circuit:
    def __init__(self):
        self.rows = []
    def gate(self,op,x,y,name=None):
        name = name or 'r'+str(len(self.rows)+1)
        self.rows.append([name,op,x,y])
        return name
    def add(self,x,y,name=None):
        return self.gate('+',x,y,name)
    def sub(self,x,y,name=None):
        return self.gate('-',x,y,name)
    def mul(self,x,y,name=None):
        return self.gate('*',x,y,name)
    def square(self,x,name=None):
        return self.mul(x,x,name)


def build():
    circ = Circuit()
    add,sub,mul,sq = circ.add,circ.sub,circ.mul,circ.square
    qm1 = mul('beta','J','qm1'); q = add(qm1,1,'q')
    q2 = sq(q,'q2'); q3 = mul(q2,q,'q3'); q4 = sq(q2,'q4')
    U = mul(4,q4,'U'); X = mul('w',q,'X'); Y = mul('s',q3,'Y')
    E = mul(X,Y,'E'); k = add('eta','zeta','k')
    kY = mul(k,Y,'kY'); c = add(kY,'eta','c'); a = add(E,Y,'a')
    H = add(mul(4,a),3,'H'); Delta = add(sq(a),H,'Delta')
    ell = mul(E,kY,'ell'); A1 = add(mul(ell,add(ell,k)),1,'A1')
    c2 = sq(c,'c2'); G = add(mul(Delta,c2),1,'G')
    b0 = add(X,mul(a,c),'b0')
    qF = sub(q,'F','qF'); Cw = sub(qF,'alpha','Cw')
    R = add(mul(add(mul(qm1,qF),'alpha'),sub(q2,1)),
            mul(add('MC',mul(q,'MF')),'J'),'R')
    Nt = sub(add(mul(add('K0','w'),Cw),qF),mul('z',qm1),'Nt')
    r = sub(sub(k,R),1,'r')
    Dstar = add(mul(U,b0),mul(H,sub(mul(U,'gamma'),r)),'Dstar')
    Nmain = sub(sq(Dstar),mul(sq(U),G),'Nmain')
    I = mul('i',c2,'I'); I2 = sq(I,'I2'); f2 = sq('f','f2')
    Q = mul(Delta,sub(f2,1),'Q'); d = sub(Q,1,'d')
    Ns = sub(I2,d,'Ns')
    V = sub(mul(c,sub(mul('T','f'),1)),mul(R,f2),'V')
    x = add('t',ell,'x'); x2 = sq(x,'x2')
    Eaux = sub(mul(Q,sq(V)),1,'Eaux')
    delta = sub(x2,A1,'delta')
    core = sub(mul(d,delta),Eaux,'core')
    N = sub(sq(core),mul(4,mul(mul(d,A1),Eaux)),'N')
    P = sub(mul(mul(mul(Nt,add(Nmain,1)),Ns),add(N,1)),1,'P13')
    names = set(VARIABLES+PORTS)
    for name,op,left,right in circ.rows:
        require(name not in names,'Repeated register '+name)
        require(op in ('+','-','*'),'Nonbinary arithmetic')
        require(all(type(v) is int or v in names for v in (left,right)), 'Undefined input')
        names.add(name)
    live = {P}
    for name,op,left,right in reversed(circ.rows):
        require(name in live, 'Dead register '+name)
        live.update(v for v in (left,right) if isinstance(v,str))
    require(set(VARIABLES+PORTS) <= live, 'Unused witness or coefficient')
    counts = Counter(row[1] for row in circ.rows)
    packet = {'name':'root_centered13_degree114', 'domain':'strictly positive integers',
              'witnesses':VARIABLES, 'fixed_numerals':PORTS,
              'source':circ.rows, 'output':P, 'exact_degree':114,
              'coefficient_binding':'COEFFICIENT_BINDING.json', 'proof':'PROOF.md',
              'ledger':{'operations':len(circ.rows),'multiplications':counts['*'],
                        'additions':counts['+'],'subtractions':counts['-'],
                        'all_gates_live':True,'all_inputs_live':True,
                        'convention':'Each binary +, -, or * counts once, including scalar multiplication and squaring; fixed leaves and register reuse are free.'},
              'exact_degree_certificate':{'upper_bound_identity':'N=d^2*(x^2-A1)^2-2*d*(x^2+A1)*Eaux+Eaux^2',
                                          'diagonal_degree':114,
                                          'diagonal_leading_coefficient':'2^19*beta^67'},
              'status':'Ordinary mathematical reduction with explicit inherited compiler; no new kernel certificate.'}
    (ROOT/'polynomial.json').write_text(json.dumps(packet,indent=2)+'\n')
    (ROOT/'BUILD_RECEIPT.json').write_text(json.dumps(packet['ledger'],indent=2)+'\n')
    print(json.dumps(packet['ledger'],indent=2))


if __name__ == '__main__':
    build()
