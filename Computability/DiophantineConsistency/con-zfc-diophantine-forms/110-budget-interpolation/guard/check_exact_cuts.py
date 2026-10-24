#!/usr/bin/env python3
"""Exact integer-polynomial equality of every delivered front register.
Each cut treats its direct named dependencies as independent indeterminates.
Induction through the acyclic register dependencies proves full front equality.
"""
import ast,json
from pathlib import Path
from exact_polynomial import Ring
from audit_support import require
ROOT=Path(__file__).resolve().parent
FORMULAS={
'J':'1+6*j','q':'1+beta*J','W':'4*(3*w+1)',
'X':'W*q','Y':'v*q','E':'X*Y','a':'(X+1)*Y','H':'4*a+3','Delta':'(a+1)*(a+3)',
'F':'K0*C+W*C-z*q+z','alpha':'q-C-F',
'R':'((q-1)*(q-F)+alpha)*(q*q-1)+(MC+MF*q)*J',
'k':'1+R+h*E','eta':'c-Y*k','c2':'c*c','I':'(2*r+1)*c2',
'I2':'I*I','Bstrong':'Delta*I2','Df':'1+Bstrong','Q':'Delta*Bstrong','delta':'Q-1',
'V':'Df*c*T-Df*R-c','Cy':'Q*V**2-1','ell0':'X*Y*Y','L':'ell0*k',
'Dtau':'L*L+L*k+1','Dmain':'1+Delta*c2','b0':'a*c+X',
'coneU':'cone_A*F','coneZ':'cone_B*C',
'Derr':'(coneU-q)**2+(coneZ-q)**2',
'budget':'(q*k)**2-k*k*Derr-(2*q*eta)**2',
'Ag':'budget-(1+p2*p2+p3*p3+p3)',
'M':'2*q*q','U':'M*H','U2':'U*U',
'scaled_Df':'U2*Df','scaled_Dtau':'U2*Dtau','scaled_Dmain':'M*M*Dmain',
'scaled_Ag':'U2*Ag','scaled_Cy':'U2*Cy',
}

def parse_expr(text,env):
    def visit(n):
        if isinstance(n,ast.Constant) and isinstance(n.value,int):return n.value
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -visit(n.operand)
        if isinstance(n,ast.BinOp):
            a,b=visit(n.left),visit(n.right)
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
            if isinstance(n.op,ast.Pow):return a**b
        raise ValueError('unrecognized syntax')
    return visit(ast.parse(text,mode='eval').body)

def exact_cut(packet,target,formula):
    syntax=ast.parse(formula,mode='eval')
    names=sorted({n.id for n in ast.walk(syntax) if isinstance(n,ast.Name)})
    ring=Ring(names);env={n:ring.var(n) for n in names};expected=parse_expr(formula,env)
    registers=dict(packet['named_registers'])
    for i,n in enumerate(packet['nodes']):
        if n[0] in ('variable','coefficient'):registers.setdefault(n[1],i)
    cuts={registers[n]:env[n] for n in names};memo={}
    def walk(i):
        if i in cuts:return cuts[i]
        if i in memo:return memo[i]
        node=packet['nodes'][i];op=node[0]
        if op=='integer':value=ring.scalar(node[1])
        elif op in ('variable','coefficient'):raise ValueError('missing dependency cut '+node[1]+' in '+target)
        else:
            a,b=walk(node[1]),walk(node[2])
            value=a+b if op=='add' else a-b if op=='sub' else a*b
        memo[i]=value;return value
    actual=walk(registers[target])
    require(actual.terms==expected.terms,'exact front cut '+target)
    return len(actual.terms)

def check_packet(packet,centered):
    formulas=dict(FORMULAS)
    # a's implementation passes through E, and R's through q(q-F)-C;
    # use the shared cut below rather than assuming their relation.
    formulas['a']='E+Y'
    formulas['R']='(q*(q-F)-C)*(q*q-1)+(MC+MF*q)*J'
    formulas['s']='U*(n+L)+M*b0+H*(v-q*q)' if centered else 'U*n+M*b0+H*(v-q*q)'
    formulas['center']='s+U*V'
    return {name:exact_cut(packet,name,formula) for name,formula in formulas.items() if name in packet['named_registers']}

def norm_cut(packet):
    from five_square_norm import cleared_norm5_compact2
    names=['x','a','b','c','d','cn','delta'];ring=Ring(names)
    aliases=['center','scaled_Df','scaled_Dtau','scaled_Dmain','scaled_Ag','scaled_Cy','delta']
    values=[ring.var(n) for n in names]
    cuts={packet['named_registers'][n]:v for n,v in zip(aliases,values)};memo={}
    def walk(i):
        if i in cuts:return cuts[i]
        if i in memo:return memo[i]
        node=packet['nodes'][i];op=node[0]
        if op=='integer':v=ring.scalar(node[1])
        elif op in ('variable','coefficient'):raise ValueError('uncut front input in norm')
        else:
            a,b=walk(node[1]),walk(node[2]);v=a+b if op=='add' else a-b if op=='sub' else a*b
        memo[i]=v;return v
    actual=walk(packet['output']);expected=cleared_norm5_compact2(*values)
    require(actual.terms==expected.terms,'exact literal norm DAG cut')
    return len(actual.terms)

def main():
    result={};norms={}
    for centered,name in ((False,'budget12_aux_centered'),(True,'budget12_tau_centered')):
        packet=json.loads((ROOT/(name+'.json')).read_text())
        result[name]=check_packet(packet,centered);norms[name]=norm_cut(packet)
    return {'exact_register_cuts':sum(len(x) for x in result.values()),'details':result,'exact_literal_norm_coefficients':norms}
if __name__=='__main__':print(json.dumps(main(),indent=2))
