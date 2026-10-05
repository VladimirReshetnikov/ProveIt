#!/usr/bin/env python3
"""Fresh complete scalar successor. No predecessor code or arrays are run."""
import argparse
from fractions import Fraction
import hashlib
import json
from math import gcd, lcm
from pathlib import Path

PINS = {
 'residue_affine_factored_counter_step.md':'60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f',
 'residue_affine_factored_counter_step.py':'0dcc6e5d4cf306037d343d7aaed8183f920c2b9e15e1b31757aadcf4606feb8a',
 'residue_affine_factored_counter_step.json':'fc8c20c02a28edcb6eaa3eed27128e282ea3835c88fc313d907c91e6e733b282',
 'markov_positive_guard_savings.md':'901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15'}
PORTS = ['n','y','z','v','P','Q','U','V']

def require(ok, msg):
    if not ok: raise ValueError(msg)

def sha(data): return hashlib.sha256(data).hexdigest()

def add(p,q,sign=1):
    out=dict(p)
    for m,c in q.items(): out[m]=out.get(m,0)+sign*c
    return {m:c for m,c in out.items() if c}

def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(x+y for x,y in zip(m,n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}

def constant(c): return {(0,)*8:c} if c else {}
def variable(j): return {tuple(int(i==j) for i in range(8)):1}
def square_sum(ps):
    out={}
    for p in ps: out=add(out,mul(p,p))
    return out
def encoded(p): return [[list(m),c] for m,c in sorted(p.items())]

def fresh_table(values):
    # Newton forward differences, converted to ordinary coefficients.
    d=list(map(Fraction,values)); basis=[Fraction(1)]; out=[Fraction(0)]*len(values)
    for j in range(len(values)):
        for k,c in enumerate(basis): out[k]+=d[0]*c
        d=[d[i+1]-d[i] for i in range(len(d)-1)]
        next_basis=[Fraction(0)]*(len(basis)+1)
        for k,c in enumerate(basis):
            next_basis[k]-=c
            next_basis[k+1]+=c/Fraction(j+1)
        # basis *= (z-(j+1))/(j+1).
        basis=next_basis
    return out

def source(K,L,coefficients):
    rows=[]
    def emit(name,op,x,y): rows.append([name,op,x,y]);return name
    table={}
    for key,cs in coefficients.items():
        current=cs[-1]
        for j in range(len(cs)-2,-1,-1):
            product=emit(key+'_product_'+str(j),'*',current,'z')
            current=emit(key+'_sum_'+str(j),'+',product,cs[j])
        table[key]=current
    I,A,D,E,p=[table[k] for k in ('I','A','D','E','p')]
    selector=emit('selector','+','z','v')
    ln=emit('Ln','*',L,'n'); kp=emit('LKP','*',L*K,'P')
    input_lhs=emit('input_lhs','+',ln,L*K);input_rhs=emit('input_rhs','+',kp,I)
    output_lhs=emit('output_lhs','*',D,'y');an=emit('An','*',A,'n')
    output_rhs=emit('output_rhs','+',an,E)
    S=emit('S','+',A,D);pL=emit('pL','+',p,L);H=emit('H','-',pL,S)
    HP=emit('HP','*',H,'P');hps=emit('HP_plus_S','+',HP,S)
    hsv=emit('HP_plus_S_plus_V','+',hps,'V');guard_lhs=emit('guard_lhs','-',hsv,2*L)
    guard_rhs=emit('guard_rhs','*',p,'Q');complement=emit('complement','+','U','V')
    pairs=[[selector,len(coefficients['I'])+1],[input_lhs,input_rhs],
           [output_lhs,output_rhs],[guard_lhs,guard_rhs],[complement,p]]
    before=len(rows)
    residuals=[emit('residual_'+str(j),'-',a,b) for j,(a,b) in enumerate(pairs)]
    squares=[emit('square_'+str(j),'*',r,r) for j,r in enumerate(residuals)]
    total=squares[0]
    for j in range(1,5): total=emit('join_'+str(j),'+',total,squares[j])
    return rows,pairs,residuals,total,before

def expand_own(rows):
    env={s:variable(j) for j,s in enumerate(PORTS)}
    for name,op,x,y in rows:
        p=constant(x) if type(x) is int else env[x]
        q=constant(y) if type(y) is int else env[y]
        env[name]=mul(p,q) if op=='*' else add(p,q,1 if op=='+' else -1)
    return env

def eval_own(rows,values,output):
    env=dict(zip(PORTS,values))
    for dest,op,a,b in rows:
        x=a if type(a) is int else env[a];y=b if type(b) is int else env[b]
        env[dest]=x*y if op=='*' else x+y if op=='+' else x-y
    return env[output]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    dependencies={}
    for name,pin in PINS.items():
        data=(args.root/name).read_bytes();require(sha(data)==pin,'dependency '+name)
        dependencies[name]={'sha256':pin,'bytes':len(data),'executed_or_imported':False}
    # A literal new transcription of the parent fixture's instruction DATA.
    K=11; primes=[2,3,5]
    instructions={1:['dec',0,2,3],2:['inc',1,1],3:['dec',1,4,5],
                  4:['inc',2,3],5:['dec',2,5,6],6:['inc',0,6]}
    instructions.update({j:['inc',0,j] for j in range(7,12)})
    branches=[]
    for state in range(1,K+1):
        ins=instructions[state];p=primes[ins[1]];require(gcd(p,K)==1,'coprime')
        cases=[('inc',p,1,ins[2])] if ins[0]=='inc' else [('dec',1,p,ins[2]),('zero',1,1,ins[3])]
        for kind,A,D,target in cases:
            branches.append({'I':state,'A':A,'D':D,'E':A*(K-state)-D*(K-target),
                             'p':p,'kind':kind,'target':target})
    rational={key:fresh_table([b[key] for b in branches]) for key in ('I','A','D','E','p')}
    L=lcm(*(v.denominator for cs in rational.values() for v in cs))
    coefficients={key:[int(L*c) for c in cs] for key,cs in rational.items()}
    prior=json.loads((args.root/'residue_affine_factored_counter_step.json').read_bytes())['counter']
    require(L==prior['interpolation_denominator'] and coefficients==prior['coefficient_rows'],'independent table reconstruction')
    for j,b in enumerate(branches,1):
        for key,cs in coefficients.items():
            require(sum(c*j**i for i,c in enumerate(cs))==L*b[key],'table entry')
    B=len(branches);rows,pairs,residuals,output,before=source(K,L,coefficients)
    require((prior['branches'],prior['graph_operations'],prior['polynomial_operations'])==(B,10*B+8,10*B+22),'actual parent ledger')
    seen=set(PORTS);by={}
    for dest,op,a,b in rows:
        require(dest not in seen and all(type(x) is int or x in seen for x in (a,b)),'topology')
        seen.add(dest);by[dest]=(a,b)
    live=set();pending=[output]
    while pending:
        x=pending.pop()
        if type(x) is str and x not in live:
            live.add(x);pending.extend(by.get(x,()))
    require(live==seen,'structural liveness')
    M=sum(r[1]=='*' for r in rows);A=len(rows)-M
    graphM=sum(r[1]=='*' for r in rows[:before]);graphA=before-graphM
    require((graphM,graphA,M,A)==(5*B+1,5*B+6,5*B+6,5*B+15),'complete ledgers')
    env=expand_own(rows);v={s:variable(j) for j,s in enumerate(PORTS)}
    table={key:sum_poly_z(cs) for key,cs in coefficients.items()}
    I,AA,D,E,p=[table[k] for k in ('I','A','D','E','p')]
    S=add(AA,D);H=add(add(p,constant(L)),S,-1)
    r4=add(add(add(mul(H,v['P']),S),v['V']),constant(2*L),-1)
    r4=add(r4,mul(p,v['Q']),-1)
    r5=add(add(v['U'],v['V']),p,-1)
    expected=[add(add(v['z'],v['v']),constant(B+1),-1),
              add(add(mul(constant(L),v['n']),constant(L*K)),add(mul(constant(L*K),v['P']),I),-1),
              add(mul(D,v['y']),add(mul(AA,v['n']),E),-1),r4,r5]
    require([env[r] for r in residuals]==expected,'full residual identities')
    new=square_sum(expected);require(env[output]==new,'full output identity')
    # Old polynomial is a displayed mathematical formula, never an old source evaluation.
    old_guard=add(r4,r5,-1);old=square_sum(expected[:3]+[old_guard,r5])
    correction=add(mul(constant(2),mul(old_guard,r5)),mul(r5,r5))
    require(add(new,old,-1)==correction,'full all-ring correction')
    degree=max(map(sum,new));require(degree==2*B,'exact fixture degree')
    # Pure control/table checks and new-source execution only.
    valid=wrong=0
    for n in range(1,111):
        P=(n-1)//K+1;state=(n-1)%K+1;ins=instructions[state];p0=primes[ins[1]]
        if ins[0]=='inc': payload=P*p0;target=ins[2]
        elif P%p0==0: payload=P//p0;target=ins[2]
        else: payload=P;target=ins[3]
        y=K*(payload-1)+target
        for j,b in enumerate(branches,1):
            h=b['p']+1-b['A']-b['D'];Z=h*P+b['A']+b['D']-2
            rem=Z%b['p'];Q=Z//b['p']+1;U=L*(rem or 1);V=L*(b['p']-(rem or 1))
            wanted=(b['I']==state and (b['kind']=='inc' or (P%b['p']==0)==(b['kind']=='dec')))
            for candidate_y in sorted({max(1,y-1),y,y+1}):
                values=[n,candidate_y,j,B+1-j,P,Q,U,V]
                require((eval_own(rows,values,output)==0)==(wanted and candidate_y==y),'fresh complete source cases')
                if wanted and candidate_y==y: valid+=1
                else: wrong+=1
    result={'schema':'residue-affine-complement-reuse-v1','helper_sha256':sha(Path(__file__).read_bytes()),
            'dependencies':dependencies,'K':K,'register_primes':primes,'instructions':instructions,
            'branches':branches,'B':B,'L':L,'coefficient_rows':coefficients,'ports':PORTS,
            'external_positive_integer_ports':['n','y'],'positive_witnesses':PORTS[2:],
            'source':rows,'equation_sides':pairs,'graph_row_count':before,'residuals':residuals,'output':output,
            'graph_counts':{'M':graphM,'A':graphA,'total':before},
            'polynomial_counts':{'M':M,'A':A,'total':len(rows),'exact_degree':degree},
            'full_output_coefficients':encoded(new),'residual_coefficients':[encoded(p) for p in expected],
            'full_correction':'new-old = 2*old_guard*complement_residual + complement_residual^2',
            'checks':{'table_values':5*B,'full_residual_identities':5,'full_output_identity':True,
                      'all_ring_correction':True,'positive_true_cases':valid,'false_cases':wrong,'all_ports_rows_live':True},
            'scope':{'all_program_theorem':'companion Markdown','saved_fixture_is_universal':False,
                     'predecessor_execution_import':False,'predecessor_array_evaluation':False,
                     'new_source_only_executed':True,'ordinary_prime_power_loader_paid':False,
                     'fixed_arity_unbounded_history_claim':False,'global_optimality_claim':False},'status':'PASS'}
    with args.output.open('x',encoding='utf-8') as f: json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'status':'PASS','graph':before,'polynomial':len(rows),'M':M,'A':A,'degree':degree,'positive':valid,'false':wrong}))

def sum_poly_z(cs):
    result={}
    for j,c in enumerate(cs):
        if c: result[(0,0,j,0,0,0,0,0)]=c
    return result

if __name__=='__main__': main()
