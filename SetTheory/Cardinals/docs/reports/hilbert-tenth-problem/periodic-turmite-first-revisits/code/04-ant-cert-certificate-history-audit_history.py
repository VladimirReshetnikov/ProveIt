#!/usr/bin/env python3
"""Recovered own data-only DAG replay, finite outer simulation, mutation checks.
Only the newly authored reconstruct_history module is imported.
"""
from pathlib import Path
from itertools import product
from copy import deepcopy
import json
import reconstruct_history as own
ROOT=Path(__file__).resolve().parent

def need(p,m):
    if not p:raise ValueError(m)

def evaluate(data,inputs):
    env=dict(inputs)
    for out,op,a,b in data['nodes']:
        a=a if type(a) is int else env[a];b=b if type(b) is int else env[b]
        env[out]=a+b if op=='+' else a-b if op=='-' else a*b
    return env

def value(cells):return sum(bit*3**index for index,bit in enumerate(cells))

def simulate(data,initial,start,steps):
    width,height=3,2;area=width*height;board=list(initial);position=start;heading=0
    fields={k:0 for k in ['A','B','C','D','E','F','G','GE','GW','GN','GS','Z']}
    for t in range(steps):
        old=board[position];out=(heading+1-2*old)%4
        x,y=position%width,position//width
        dx,dy=[(0,-1),(1,0),(0,1),(-1,0)][out]
        if not(0<=x+dx<width and 0<=y+dy<height):return None
        head=3**position;scale=3**(area*t);sign=heading//2
        local={'A':value(board),'C':head,'Z':sign*head,'D':old*head,'E':(1-old)*head,
               'F':old*sign*head,'G':old*(1-sign)*head,'GE':0,'GW':0,'GN':0,'GS':0}
        local[['GN','GE','GS','GW'][out]]=head
        board[position]=1-old;local['B']=value(board)
        for k,v in local.items():fields[k]+=scale*v
        position=(y+dy)*width+x+dx;heading=out
    W=3**width;Q=W**height;q=Q**steps
    wits=dict.fromkeys(data['witnesses'],1)
    wits.update(q=q,Q=Q,W=W,uQ=q//Q,uW=Q//W,Gt=(q-1)//(Q-1),Gy=(Q-1)//(W-1),
                WidthOdd=(W-3)//8,HeightEven=(Q-1)//(W*W-1),K=(q-1)//8,Wp=W//3,
                HeadRoot=3**(start//2),HeadQuot=q//(3**start),BoundInitial=Q-value(initial),BoundHead=Q-3**start)
    for k in own.RAW:
        v=fields[k] if k not in ['SW','SN'] else fields['GW']//3 if k=='SW' else fields['GN']//W
        wits[k+'Plus']=v+1
    pars=dict(InitialMemoryPlus=value(initial)+1,FinalMemoryPlus=value(board)+1,InitialHead=3**start,FinalHead=3**position,FinalSignPlus=1+(heading//2)*3**position)
    env=evaluate(data,dict(wits,**pars))
    for k in own.FIELDS+['Z']:wits['Bound'+k]=q-env[k]
    wits['r']=env['mask_r']
    need(all(type(v) is int and v>0 for v in wits.values()),'nonpositive outer witness')
    env=evaluate(data,dict(wits,**pars))
    for ix,(l,r) in enumerate(data['equalities'][:38]):need(env[l]==env[r],'outer residual '+str(ix))
    P=env[data['exports']['P']];need(0<=P<q**16 and P%2==0,'packed bound/parity')
    rest=P
    while rest:
        rest,digit=divmod(rest,3);need(digit in [0,1],'non-Boolean packing')
    def v3factorial(n):
        ans=0
        while n:n//=3;ans+=n
        return ans
    r=wits['r'];val=v3factorial(2*r)-2*v3factorial(r)
    need(val==16*area*steps+2,'exact central-binomial valuation')
    return {'initial':value(initial),'start':start,'steps':steps,'final':value(board),'end':position,'valuation':val}

def main():
    data=json.loads((ROOT/'history174.json').read_text());receipt=own.check(data)
    attempts=0;passed=[]
    for initial in product([0,1],repeat=6):
        for start in [0,2,4]:
            for steps in range(1,5):
                attempts+=1;row=simulate(data,initial,start,steps)
                if row is not None:passed.append(row)
    modifications={
      'undeclared operand':lambda d:d['nodes'][0].__setitem__(2,'not_declared'),
      'changed constant':lambda d:d['nodes'][0].__setitem__(3,2),
      'wrong arithmetic':lambda d:d['nodes'][0].__setitem__(1,'+'),
      'duplicate output':lambda d:d['nodes'][1].__setitem__(0,d['nodes'][0][0]),
      'forward reference':lambda d:d['nodes'][0].__setitem__(2,d['nodes'][-1][0]),
      'changed equality':lambda d:d['equalities'][0].__setitem__(1,'Q'),
      'changed numeral list':lambda d:d.__setitem__('fixed_numerals',[1,3]),
      'changed witness domain':lambda d:d['witnesses'].__setitem__(0,'UnknownPlus'),
      'Boolean instead of integer':lambda d:d['nodes'][0].__setitem__(3,True),
      'deleted operation':lambda d:d['nodes'].pop(),
    }
    rejected=[]
    for name,change in modifications.items():
        mutated=deepcopy(data);change(mutated)
        try:own.check(mutated)
        except (ValueError,KeyError,TypeError):rejected.append(name)
        else:raise ValueError('accepted mutation '+name)
    out=dict(status='PASS',serialized_dag_rechecked=True,finite_histories_attempted=attempts,
             bounded_histories_verified=len(passed),genuine_outer_equalities_per_history=38,
             all_positive_outer_witnesses=True,packed_even_boolean_and_exact_valuation=True,
             mutation_rejections=rejected,samples=passed[:12],
             scope='Finite exact regression and adversarial data validation, not an all-integer proof. No enormous Pell tuple is constructed; Pell completeness remains the pinned theorem dependency.')
    (ROOT/'audit_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
