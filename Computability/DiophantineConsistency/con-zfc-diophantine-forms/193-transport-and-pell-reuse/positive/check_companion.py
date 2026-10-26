"""Exact companion audit from free polynomial identities, separate from producer."""
from collections import Counter
from pathlib import Path
import json
from check_independent import Poly,var,quotient_A,require,load_coefficients,dependence_certificate

ROOT=Path(__file__).resolve().parent

def check(equation,parent):
    for key in ('domain','witnesses','fixed_numerals','output'):
        require(equation[key]==parent[key],'Changed companion interface: '+key)
    rows=equation['source']
    require(len(rows)==equation['operations']==99,'Companion operation count')
    require(dict(Counter(r[1] for r in rows))==equation['operation_breakdown'],'Companion operation split')
    by={};known=set(equation['witnesses']+equation['fixed_numerals'])
    for name,op,left,right in rows:
        require(name not in known and op in ('+','-','*'),'Bad companion DAG')
        require(all(isinstance(x,int) or x in known for x in (left,right)),'Unknown operand')
        known.add(name);by[name]=[name,op,left,right]
    live={equation['output']}
    for name,op,left,right in reversed(rows):
        if name in live:live.update(x for x in (left,right) if isinstance(x,str))
    require(set(by)|set(equation['witnesses']+equation['fixed_numerals']) <=live,'Dead companion input/gate')
    for row in parent['source']:
        name=row[0]
        if name=='L':require(name not in by,'Unremoved transport')
        elif name not in ('LBt','RG'):require(by.get(name)==row,'Changed companion parent row: '+name)
    require(by['LBt']==['LBt','*','V','new_bBcenter'],'Wrong factored carrier')
    require(by['RG']==['RG','*','M2','new_scaledG'],'Wrong norm port')
    A,y0,k,U,b,c,B=[var(j) for j in range(7)]
    v=y0*(A-y0-1);ell=k*v;E=1+k*k*v*(v+1)
    Delta=A*A-1;G=E*(1+Delta*U*U*E)
    V=(1+2*Delta*U*U*E)*b-c
    S=quotient_A(E,1);RE=E-A*S;C2=2*A*U*E-U*S
    vals=dict(Am1=A-1,k=k,qY=y0,V0kk=ell+k,U=U,Dtau=E,
              UE=U*E,cTR=b,Bt=B,Dg=G)
    count=0
    for name,op,left,right in rows:
        if not name.startswith('new_'):continue
        count+=1
        def get(x):return Poly(x) if isinstance(x,int) else vals[x]
        x,y=get(left),get(right)
        vals[name]=x+y if op=='+' else x-y if op=='-' else x*y
    require(count==13,'Unclassified companion rows')
    require(vals['new_gcenter']==C2,'False quotient center')
    require(vals['new_bBcenter']==b*B+C2,'False carrier factor')
    require(vals['new_scaledG']==4*G,'False root scale')
    defect=C2*C2-4*G
    require(defect==4*U*U*E*RE+U*U*S*S-4*E,'False norm defect identity')
    weights=(4,2,1,5,4,2,2)
    require(defect.degree(weights)==34,'Companion defect degree')
    expected=4*A*A*y0**6*k**4*U*U
    require(defect.top(weights)==expected,'Wrong defect top')
    q0,w,s,i,eta,zeta,F=[var(j) for j in range(7)];k0=eta+zeta
    A0=q0*q0*w*s;y00=q0*s;U0=i*k0*k0*s*s;b0=-q0**3*(q0-F)
    E0=k0*k0*q0**6*w*w*s**4
    Q0=4*A0**6*U0**4*E0**2;M0=24*q0**10*w*s
    V0=2*A0*A0*U0*U0*E0*b0
    ptop=Q0*M0*M0*V0*V0*expected.substitute([A0,y00,k0,U0,b0,0,0])
    claimed=9*2**12*q0**80*w**22*s**56*i**10*k0**32*(q0-F)**2
    require(ptop==claimed and ptop.degree((1,)*7)==202,'Wrong full companion degree')
    return {'operations':99,'operation_breakdown':equation['operation_breakdown'],
            'new_rows':13,'defect_degree':34,'exact_degree':202,'highest_form_terms':len(ptop.d)}

if __name__=='__main__':
    parent=json.loads((ROOT/'parent87.json').read_text())
    equation=json.loads((ROOT/'quotient202.json').read_text())
    result=check(equation,parent)
    result['actual_input_dependence']=dependence_certificate(equation,load_coefficients(equation))
    print(json.dumps(result,indent=2))
