#!/usr/bin/env python3
"""Exact identities and source-parsed machine checks.

Python 3.10+ and SymPy. Run from any directory. Finite tests supplement the
all-input arguments in the editorial notes; a simulation cutoff is never
reported as a proof of nontermination.
Reads the current sources (Papers/1982, Papers/1984).
"""
from __future__ import annotations
import itertools, json, math, re
from pathlib import Path
import sympy as sp
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def need(value, message):
    if not value: raise AssertionError(message)

def parse_program():
    text=(ROOT/'1984/jones1984_corrected.tex').read_text(encoding='utf-8')
    pos=text.index(r'\textbf{Example 1.}')
    start=text.index(r'\begin{array}',pos); stop=text.index(r'\end{array}',start)
    rows=re.findall(r'^L\s+(\d+)\s*&\s*(.*)$',text[start:stop],re.M)
    need([int(i) for i,_ in rows]==list(range(15)), 'Expected fifteen source program lines')
    program=[]
    for pc,body in rows:
        if r'\leftarrow' in body:
            assigns=re.findall(r'R\s*(\d+)\s*\\leftarrow\s*R\s*(\d+)\s*([+-])1',body)
            need(assigns, 'Unparsed assignment')
            need(all(a==b for a,b,_ in assigns),'Non-local register assignment')
            need(len({a for a,_,_ in assigns})==len(assigns),'Conflicting parallel assignments')
            program.append(('assign',[(int(a)-1,1 if op=='+' else -1) for a,b,op in assigns]))
        elif 'IF' in body:
            cond=re.search(r'(R\s*[1-4]|0)\s*([<=])\s*(R\s*[1-4]|0)',body)
            targets=re.findall(r'L\s*(\d+)',body)
            need(cond is not None and len(targets)==1,'Unparsed conditional transfer')
            def operand(s): return ('const',0) if s=='0' else ('reg',int(re.search(r'\d',s)[0])-1)
            program.append(('if',(operand(cond[1]),cond[2],operand(cond[3]),int(targets[0]))))
        elif 'GO TO' in body:
            program.append(('goto',int(re.search(r'L\s*(\d+)',body)[1])))
        elif 'STOP' in body: program.append(('stop',None))
        else: raise AssertionError('Unparsed source line '+pc)
    return program

def run_machine(program,x,limit):
    regs=[x,0,0,0]; pc=0; seen=set(); transitions=0; samples=[]
    while transitions<=limit:
        state=(pc,tuple(regs))
        if state in seen: return 'cycle',transitions,state,samples
        seen.add(state)
        if pc==9:
            r1,k,multiple,r4=regs
            need(k>=2 and r1==x and r4==0 and multiple>0 and multiple%k==0,
                 'Trial-division invariant failed')
            if x<2: samples.append(k)
        op,arg=program[pc]
        if op=='stop': return 'halt',transitions,state,samples
        nxt=pc+1; old=regs[:]
        if op=='assign':
            for j,d in arg:
                need(old[j]+d>=0,'Subtraction from zero')
                regs[j]=old[j]+d
        elif op=='goto': nxt=arg
        elif op=='if':
            a,cmp,b,target=arg
            val=lambda t: old[t[1]] if t[0]=='reg' else t[1]
            condition=(val(a)==val(b)) if cmp=='=' else (val(a)<val(b))
            if condition: nxt=target
        else: raise AssertionError('Unknown opcode')
        pc=nxt; transitions+=1
    return 'limit',transitions,(pc,tuple(regs)),samples

def machine_tests():
    program=parse_program(); outcomes=[]
    for x in range(2,129):
        result,steps,state,_=run_machine(program,x,300000)
        prime=all(x%d for d in range(2,math.isqrt(x)+1))
        need(result==('halt' if prime else 'cycle'),f'Machine classification failed at {x}')
        if prime: need(state==(14,(0,0,0,0)), 'Nonzero accepting state')
        else:
            need(state[0]==10 and state[1][2]==x and 2<=state[1][1]<x,
                 'Composite did not reach proper-divisor trap')
        if x==2: need(steps==18,'Wrong trace length for input 2')
        outcomes.append({'input':x,'status':result,'transitions':steps})
    boundaries=[]
    for x in (0,1):
        result,steps,state,samples=run_machine(program,x,20000)
        need(result=='limit' and len(samples)>20, 'Unexpected boundary behavior')
        need(samples==list(range(2,2+len(samples))), 'Non-increasing boundary trial values')
        boundaries.append({'input':x,'status':'finite prefix only','transition_limit':20000,
                           'completed_trials':len(samples)})
    return {'source_lines_parsed':15,'input_range':'2..128','outcomes':outcomes,
            'boundary_runs':boundaries,
            'scope':'Source-parsed simulation and invariant checks. The proof of nontermination for inputs 0,1 is in the editorial report, not inferred from the cutoff.'}

def convolution(a,b):
    result={}
    for i,u in a.items():
        for j,v in b.items(): result[i+j]=result.get(i+j,0)+u*v
    return {k:v for k,v in result.items() if v}

def coefficient_tests():
    tex=(ROOT/'1982/jones1982_corrected.tex').read_text(encoding='utf-8')
    need(r'B=2b^{\delta}(2z)^{(\delta+1)^{\nu+1}+1}' in tex, 'D2 source changed')
    cases=roots=0
    for nu in (1,2):
        delta=4; L=5**(nu+1); K=5**nu
        xs=sp.symbols('x:'+str(nu+1)); x,w=xs[:2]
        tail=sum(v*v for v in xs[2:])
        expressions=[(x-1)**2+w*w+tail,
                     (x*x-w)**2+(w-1)**2+tail,
                     (x+w-2)**2+(x*w-1)**2+tail]
        indices=[t for t in itertools.product(range(delta+1),repeat=nu+1) if sum(t)<=delta]
        for expression in expressions:
            p=sp.Poly(expression,*xs)
            scaled={t:int(p.coeff_monomial(t))*math.prod(math.factorial(i) for i in t)
                        *math.factorial(delta-sum(t)) for t in indices}
            z=2
            while not z>1+max(map(abs,scaled.values())): z*=2
            minus_D={j:-z for j in range(L+1)}
            for t,pi in scaled.items():
                j=L-sum(i*5**a for a,i in enumerate(t))
                minus_D[j]+=z+pi
            need(all(abs(v)<=z for v in minus_D.values()), 'Coefficient premise failed')
            for b in (2,4):
                B=2*b**delta*(2*z)**(L+1)
                need(B&(B-1)==0,'Base is not a power of two')
                Q=B**L
                for values in itertools.product(range(b),repeat=nu+1):
                    c={0:1}
                    c.update({5**i:v for i,v in enumerate(values) if v})
                    cp={0:1}
                    for _ in range(delta): cp=convolution(cp,c)
                    h=convolution(cp,minus_D)
                    pvalue=int(p.eval(dict(zip(xs,values))))
                    need(h.get(L,0)==math.factorial(delta)*pvalue,'Central coefficient mismatch')
                    need(max(h,default=0)<=delta*K+L<2*L,'Degree support bound failed')
                    bound=z*(nu+2)**delta*b**delta
                    need(all(abs(v)<bound<B//2 for v in h.values()),'Strict coefficient bound failed')
                    digits=[h.get(j,0)+B//2 for j in range(2*L)]
                    need(all(0<d<B for d in digits),'Offset did not produce base-B digits')
                    encoded=0
                    for d in reversed(digits): encoded=encoded*B+d
                    mask=(B//2-1)*Q
                    need((encoded & mask == 0)==(pvalue==0),'Zero-detection mask failed')
                    cases+=1; roots+=int(pvalue==0)
    return {'cases':cases,'zero_cases':roots,'delta':4,'nu':[1,2],'ceilings':[2,4],
            'polynomials_per_arity':3,
            'scope':'Exact coefficient extraction, strict no-carry inequalities and actual integer bit-mask checks for six test polynomials; general proof is in the report.'}

def normalization_and_bounds():
    cases=0
    for p in range(21):
        for t in range(21):
            need((p+(t-1)**2==0)==(p==0 and t==1),'Normalization equivalence failed')
            cases+=1
    need(-1+(0-1)**2==0,'Missing negative-polynomial counterexample')
    for n in range(2,257):
        need(4*(4*n+4)**(2*n-1)>(4*n)**(2*n-2),'Halting-count interval separation failed')
    for nu in range(1,257):
        need(nu+2<=2**(nu+1),'Elementary exponential bound failed')
        for delta in range(3,11):
            need(delta*(nu+1)<(delta+1)**(nu+1),'Bernoulli bound failed')
    return {'normalization_pairs':cases,'negative_p_counterexample':{'p':-1,'t':0},
            'halting_count_interval_tests':'2<=n<=256',
            'coefficient_inequality_parameters':'1<=nu<=256; 3<=delta<=10',
            'scope':'Finite checks of inequalities and the normalization boundary; see the report for general arguments.'}

def main():
    report={'status':'PASS','prime_machine':machine_tests(),
            'coefficient_encoding':coefficient_tests(),
            'normalization_and_bounds':normalization_and_bounds()}
    (HERE/'corpus_review_results.json').write_text(json.dumps(report,indent=2)+'\n',
                                                       encoding='utf-8',newline='\n')
    brief={**report,'prime_machine':{k:v for k,v in report['prime_machine'].items() if k!='outcomes'}}
    print(json.dumps(brief,indent=2))

if __name__=='__main__': main()
