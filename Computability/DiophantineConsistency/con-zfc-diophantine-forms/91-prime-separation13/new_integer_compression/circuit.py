#!/usr/bin/env python3
"""Emit and count a deterministic shared binary arithmetic DAG.

Every live addition, subtraction, multiplication and square on witnesses costs
one. Fixed-numeral arithmetic is precomputed and its recipes are recorded.
This is a reproducible supplied circuit, not a minimal-operation claim.
"""
from pathlib import Path
import ast, json

ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

class DAG:
    def __init__(self,variables,ports,definitions):
        self.variables=variables;self.ports=ports;self.definitions=definitions
        self.nodes=[];self.fixed=[];self.memo={};self.regs={};self.const={}
        for v in variables:self.const['v:'+v]=False
        for p in ports:self.const['c:'+p]=True
    def lit(self,n):
        key='n:'+str(n);self.const[key]=True;return key
    def op(self,op,a,b):
        if op in ('add','mul') and a>b:a,b=b,a
        if op=='add' and a=='n:0':return b
        if op=='add' and b=='n:0':return a
        if op=='sub' and b=='n:0':return a
        if op=='sub' and a==b:return self.lit(0)
        if op=='mul' and (a=='n:0' or b=='n:0'):return self.lit(0)
        if op=='mul' and a=='n:1':return b
        if op=='mul' and b=='n:1':return a
        if a.startswith('n:') and b.startswith('n:'):
            x,y=int(a[2:]),int(b[2:]);return self.lit(x+y if op=='add' else x-y if op=='sub' else x*y)
        key=(op,a,b)
        if key in self.memo:return self.memo[key]
        fixed=self.const[a] and self.const[b]
        seq=self.fixed if fixed else self.nodes
        out=('k:' if fixed else 'g:')+str(len(seq))
        seq.append({'id':out,'op':op,'left':a,'right':b})
        self.memo[key]=out;self.const[out]=fixed
        return out
    def power(self,a,n):
        if n==0:return self.lit(1)
        if n==1:return a
        half=self.power(a,n//2);sq=self.op('mul',half,half)
        return self.op('mul',sq,a) if n%2 else sq
    def parse(self,expression):
        def f(n):
            if isinstance(n,ast.Constant):return self.lit(n.value)
            if isinstance(n,ast.Name):
                if n.id in self.variables:return 'v:'+n.id
                if n.id in self.ports:return 'c:'+n.id
                if n.id not in self.regs:self.regs[n.id]=self.parse(self.definitions[n.id])
                return self.regs[n.id]
            if isinstance(n,ast.UnaryOp):return self.op('sub',self.lit(0),f(n.operand))
            a=f(n.left)
            if isinstance(n.op,ast.Pow):return self.power(a,n.right.value)
            b=f(n.right)
            op='add' if isinstance(n.op,ast.Add) else 'sub' if isinstance(n.op,ast.Sub) else 'mul'
            return self.op(op,a,b)
        return f(ast.parse(expression,mode='eval').body)
    def sumsq(self,rows):
        terms=[self.op('mul',r,r) for r in rows]
        ans=terms[0]
        for t in terms[1:]:ans=self.op('add',ans,t)
        return ans
    def emit(self,name,rows,product=False):
        vals=[self.parse(r) for r in rows]
        if product:
            S=self.sumsq(vals[:-1]);G=vals[-1]
            # Expanded finalizer G+S+GS uses three operations.
            out=self.op('add',self.op('add',G,S),self.op('mul',G,S))
        else:out=self.sumsq(vals)
        live=set();table={n['id']:n for n in self.nodes+self.fixed}
        def visit(i):
            if i in live:return
            live.add(i)
            if i in table:visit(table[i]['left']);visit(table[i]['right'])
        visit(out)
        gates=[n for n in self.nodes if n['id'] in live]
        constants=[n for n in self.fixed if n['id'] in live]
        need(all('v:'+v in live for v in self.variables),'coordinate liveness')
        return {'name':name,'variables':self.variables,'fixed_ports':self.ports,
                'fixed_recipes':constants,'nodes':gates,'residual_outputs':vals,'output':out,
                'operation_count':len(gates),'operation_histogram':{o:sum(n['op']==o for n in gates) for o in ['add','sub','mul']},
                'count_convention':'one per live witness-dependent binary +,-,*; powers expanded to multiplications; fixed-numeral arithmetic precomputed; no minimality claim'}

def main():
    outputs=[]
    for name in ['norm17_degree112','center18_degree80','norm17_degree110']:
        p=json.loads((ROOT/'forms'/(name+'.json')).read_text())
        dag=DAG(p['variables'],p['fixed_numerals'],p['definitions'])
        result=dag.emit(name,p['compact_residuals'],name=='center18_degree80')
        (ROOT/'forms'/(name+'_dag.json')).write_text(json.dumps(result,indent=2)+'\n')
        outputs.append({'name':name,'operations':result['operation_count'],'histogram':result['operation_histogram']})
    (ROOT/'certificates'/'CIRCUITS.json').write_text(json.dumps(outputs,indent=2)+'\n')
    print(json.dumps(outputs,indent=2))

if __name__=='__main__':main()
