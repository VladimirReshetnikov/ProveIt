#!/usr/bin/env python3
"""Re-evaluate the unchanged fixed-prime polynomials with compact norms."""
import ast
from collections import Counter
import json
from pathlib import Path
from compact_norms import cleared_norm5

ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok: raise ValueError(message)

class Ref:
    def __init__(self,d,ref): self.d,self.ref=d,ref
    def __add__(self,b): return self.d.op('add',self,b)
    def __radd__(self,a): return self.d.op('add',a,self)
    def __sub__(self,b): return self.d.op('sub',self,b)
    def __rsub__(self,a): return self.d.op('sub',a,self)
    def __mul__(self,b): return self.d.op('mul',self,b)
    def __rmul__(self,a): return self.d.op('mul',a,self)
    def __neg__(self): return self.d.op('sub',0,self)
    def __pow__(self,n): return self.d.power(self,n)

class DAG:
    # Exactly the parent's operation normalization, including register IDs.
    def __init__(self,inputs): self.inputs,self.nodes,self.memo=list(inputs),[],{}
    def raw(self,x): return x.ref if isinstance(x,Ref) else x
    def op(self,op,a,b):
        a,b=self.raw(a),self.raw(b)
        if isinstance(a,int) and isinstance(b,int): return a+b if op=='add' else a-b if op=='sub' else a*b
        if op=='add' and (a==0 or b==0): return Ref(self,b if a==0 else a)
        if op=='sub' and b==0: return Ref(self,a)
        if op=='sub' and a==b: return 0
        if op=='mul':
            if a==0 or b==0: return 0
            if a==1 or b==1: return Ref(self,b if a==1 else a)
        if op in ('add','mul') and str(a)>str(b): a,b=b,a
        key=(op,a,b)
        if key not in self.memo:
            ref='n'+str(len(self.nodes));self.nodes.append({'id':ref,'op':op,'args':[a,b]});self.memo[key]=ref
        return Ref(self,self.memo[key])
    def power(self,a,n):
        need(type(n) is int and n>=0,'literal nonnegative exponent');r=1
        while n:
            if n&1:r=self.op('mul',r,a)
            n//=2
            if n:a=self.op('mul',a,a)
        return r
    def finish(self,out,metadata):
        out=self.raw(out);byid={n['id']:n for n in self.nodes};live=set();todo=[out]
        while todo:
            x=todo.pop()
            if isinstance(x,int) or x in live:continue
            live.add(x)
            if x in byid:todo.extend(byid[x]['args'])
        need(set(self.inputs)<=live,'all unknowns and fixed leaves live')
        nodes=[n for n in self.nodes if n['id'] in live]
        return {'representation':'division-free arithmetic DAG','inputs':self.inputs,'nodes':nodes,'output':out,
            'live_binary_operations':len(nodes),'operation_counts':dict(Counter(n['op'] for n in nodes)),**metadata}

def parse(expr,d,values):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return n.value
        if isinstance(n,ast.Name):return values[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return d.op('sub',0,go(n.operand))
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Pow):
                need(isinstance(n.right,ast.Constant),'fixed exponent');return d.power(go(n.left),n.right.value)
            op={ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}.get(type(n.op));need(op is not None,'polynomial syntax')
            return d.op(op,go(n.left),go(n.right))
        raise ValueError(ast.dump(n))
    return go(ast.parse(expr,mode='eval').body)

def cleared_norm4(x,a,b,c,C,delta):
    # delta^8 F16(x;a,b,c,C/delta), grouping the first three
    # radicals a,b,C/delta and taking the outer norm over sqrt(c).
    x2=x*x;dsq=delta*delta
    q0=delta*(x2+c-a-b)-C;q1=-2*delta*x
    A0=q0*q0+c*q1*q1-4*(dsq*a*b+delta*C*(a+b))
    A1=2*q0*q1;z=64*dsq*delta*a*b*C
    f0=A0*A0+c*A1*A1-z*(x2+c)
    f1=2*A0*A1+2*z*x
    return f0*f0-c*f1*f1

def build(parent):
    d=DAG(parent['inputs']);v={n:Ref(d,n) for n in d.inputs}
    for n,e in parent['prefix_abbreviations']:v[n]=parse(e,d,v)
    boundary=len(d.nodes);old={n['id']:n for n in parent['nodes']}
    # Dead prefix records (e.g. alpha) may be absent from the stored DAG.
    old_prefix={k:n for k,n in old.items() if int(k[1:])<boundary}
    need(all(d.nodes[int(k[1:])]==n for k,n in old_prefix.items()),'literal complete prefix identity')
    if parent['root_count']==5:
        out=cleared_norm5(v['norm_z'],v['rad_A'],v['rad_B'],v['rad_D'],v['rad_G'],v['Cnum'],v['delta'])
    else:
        out=cleared_norm4(v['norm_z'],v['rad_A'],v['rad_B'],v['rad_D'],v['Cnum'],v['delta'])
    norm=d.raw(out)
    if parent['root_count']==4:out=(1+4*out)*(1+4*v['guard'])-1
    p=d.finish(out,{'name':parent['name']+'_compact','domain':parent['domain'],
        'variables':parent['variables'],'variable_count':parent['variable_count'],'fixed_ports':parent['fixed_ports'],
        'coefficient_binding':'coefficients/BINDING.json','exact_degree':parent['exact_degree'],
        'norm_output':norm,'root_count':parent['root_count'],'denominator_exponent':parent['denominator_exponent'],
        'prefix_abbreviations':parent['prefix_abbreviations'],'named_registers':{n:d.raw(x) for n,x in v.items()},
        'parent_polynomial':parent['name'],'parent_operations':parent['live_binary_operations'],
        'unchanged_prefix_boundary':boundary,'norm_rewrite':'exact generic free-radicand polynomial identity'})
    need(all(n==old[n['id']] for n in p['nodes'] if int(n['id'][1:])<boundary),'new live prefix is old literal prefix')
    need({n['id'] for n in p['nodes'] if int(n['id'][1:])<boundary}==set(old_prefix),'complete live prefix retained')
    return p

def main():
    metrics=[]
    for path in sorted((ROOT/'parent/forms').glob('integer*.json')):
        p=build(json.loads(path.read_text()));(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        metrics.append({k:p[k] for k in ('name','variable_count','exact_degree','live_binary_operations','parent_operations','operation_counts')})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':main()
