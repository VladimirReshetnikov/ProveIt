#!/usr/bin/env python3
"""Independent data-only review; imports no author or predecessor code."""
import argparse
import ast
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

AUTHOR_PINS = {
 'timed_binary_shuttle18_projection.py':'925151411f76d1f2e56ea729fed9bb5f1c1f990ff92e4920d160fe2e645b765b',
 'timed_binary_shuttle18_projection.json':'c441134593d9a593f2c599d810a6c7a48feddfb16ba85fce8d822008fa4a82bf',
 'timed_binary_shuttle18_projection.md':'5fad6c3268a1a7331387696c6b583e76a9608f0d194902c36c5dcb5977334875'}
BASE = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/'
DEPENDENCIES = {
 BASE+'code/18-timed-quartics-compact_binary_quartic.py':'9243fa208603c59285ded9d25e4493beeeadf9d90508ea7cfa615f6add7b15d4',
 BASE+'18-timed-quartics-independent-audit.md':'ce4f6cdadf548b55a00fa981f140f870ebd0fab396f164ee2a5eb4c143b50a1a'}
NAMES=('x','t','x0','x1','x2','x3','e','n','j','u')
INPUTS=list(NAMES[:6])
MODES=['four','three_literal','three_clock','two_weighted','two','two_integer_boolean']
COSTS=[(11,28),(10,26),(10,25),(9,24),(9,23),(8,23)]
ZERO=(0,)*len(NAMES)

def require(test,why):
    if not test: raise ValueError(why)
def digest(b): return hashlib.sha256(b).hexdigest()
def same(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b
def pairs(items):
    out={}
    for k,v in items:
        require(k not in out,'duplicate JSON key');out[k]=v
    return out
def read_json(p):
    return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))

class Poly:
    def __init__(self,v=0):
        if isinstance(v,Poly): self.d=dict(v.d)
        elif isinstance(v,dict): self.d={k:z for k,z in v.items() if z}
        else: self.d={ZERO:Fraction(v)} if v else {}
    def __add__(self,v):
        ans=dict(self.d)
        for k,z in Poly(v).d.items(): ans[k]=ans.get(k,0)+z
        return Poly(ans)
    __radd__=__add__
    def __neg__(self): return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,v): return self+-Poly(v)
    def __rsub__(self,v): return Poly(v)+-self
    def __mul__(self,v):
        ans={}
        for a,x in self.d.items():
            for b,y in Poly(v).d.items():
                k=tuple(z+w for z,w in zip(a,b));ans[k]=ans.get(k,0)+x*y
        return Poly(ans)
    __rmul__=__mul__
    def __eq__(self,v): return self.d==Poly(v).d
    def saved(self):
        out=[]
        for k,z in self.d.items():
            require(z.denominator==1,'integral coefficient')
            m=sorted(name for name,power in zip(NAMES,k) for _ in range(power))
            out.append([m,z.numerator])
        return sorted(out)
    def certificate(self):
        return {'terms':len(self.d),'degree':max(map(sum,self.d)),
                'sha256':digest(json.dumps(self.saved(),separators=(',',':')).encode())}

def variable(name):
    key=list(ZERO);key[NAMES.index(name)]=1;return Poly({tuple(key):Fraction(1)})
def ev_ast(node,env):
    if isinstance(node,ast.Name): return env[node.id]
    if isinstance(node,ast.Constant) and type(node.value) is int: return node.value
    if isinstance(node,ast.Tuple): return [ev_ast(x,env) for x in node.elts]
    if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub): return -ev_ast(node.operand,env)
    if isinstance(node,ast.BinOp):
        a,b=ev_ast(node.left,env),ev_ast(node.right,env)
        if isinstance(node.op,ast.Add): return a+b
        if isinstance(node.op,ast.Sub): return a-b
        if isinstance(node.op,ast.Mult): return a*b
    raise ValueError('unsupported inert formula AST')

def source_reference(text,values):
    module=ast.parse(text)
    functions=[x for x in module.body if isinstance(x,ast.FunctionDef) and x.name=='compact_binary_uniform_sos']
    require(len(functions)==1,'unique compact source constructor')
    env=dict(values)
    for name in ('d','T','residuals'):
        candidates=[s.value for s in functions[0].body if isinstance(s,ast.Assign) and len(s.targets)==1 and isinstance(s.targets[0],ast.Name) and s.targets[0].id==name]
        require(len(candidates)==1,'unique source formula '+name)
        env[name]=ev_ast(candidates[0],env)
    require(len(env['residuals'])==7,'seven original residuals')
    return env['residuals']

def evaluate(packet,values):
    free=packet['inputs']+packet['witnesses']
    require(set(values)==set(free) and len(free)==len(set(free)),'exact free interface')
    env=dict(values);edges={};counts=Counter()
    require(type(packet['source']) is list,'literal full source')
    for row in packet['source']:
        require(type(row) is list and len(row)==4,'row shape')
        name,op,l,r=row
        require(type(name) is str and name not in env and op in ('+','-','*'),'SSA')
        for q in (l,r): require(type(q) is int or (type(q) is str and q in env),'closed operands')
        a,b=(env[q] if type(q) is str else q for q in (l,r))
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
        counts[op]+=1;edges[name]=[q for q in (l,r) if type(q) is str]
    require(packet['output']==packet['source'][-1][0],'literal final output')
    live=set();pending=[packet['output']]
    while pending:
        name=pending.pop()
        if name not in live:live.add(name);pending.extend(edges.get(name,[]))
    require(live==set(env),'all rows and free ports live')
    return env,(counts['*'],counts['+']+counts['-'])

def squares(rs): return sum((r*r for r in rs),Poly())

def audit_forms(forms,original):
    require([r['packet']['mode'] for r in forms]==MODES,'six declared modes')
    report=[];full=[]
    for idx,record in enumerate(forms):
        packet=record['packet'];mode=MODES[idx]
        witnesses=['e','n','j','u'] if idx==0 else ['e','j','u'] if idx<3 else ['j','u']
        require(packet['inputs']==INPUTS and packet['witnesses']==witnesses,'coordinate interface')
        require(packet['unsquared_nonnegative_integer_rows']==(['boolean'] if idx==5 else []),'exact mixed finalizer metadata')
        values={name:variable(name) for name in INPUTS+witnesses}
        env,cost=evaluate(packet,values)
        require(cost==COSTS[idx],'independent paid ledger')
        require(packet['ledger']==dict(M=cost[0],A=cost[1],total=sum(cost)),'metadata ledger')
        mapped=dict(values)
        if idx>=3: mapped['e']=values['x2']-values['x1']-1
        if idx>=1: mapped['n']=values['x3']-values['x']-7-mapped['e']
        rs=source_reference(original,mapped)
        if idx>=1:require(rs[6]==0,'eliminated cycle equality')
        if idx>=3:require(rs[5]==rs[4],'duplicate spatial residual after phase substitution')
        wanted=squares(rs)
        if idx>=4:wanted=wanted-rs[4]*rs[4]
        if idx==5:wanted=wanted-rs[0]*rs[0]+rs[0]
        require(env[packet['output']]==wanted,'entire literal polynomial to archived formula')
        expected_res=rs[:5]+([rs[5]] if idx<4 else [])+([rs[6]] if idx==0 else [])
        # Mixed finalizer may retain the same five residual descriptors as mode two.
        require([env[r] for r in packet['residuals']]==expected_res,'all retained residual polynomials')
        require(same(record['polynomial'],wanted.saved()),'complete saved coefficients')
        require(same(record['residual_polynomials'],[z.saved() for z in expected_res]),'saved residual coefficients')
        require(record['coefficient_count']==len(wanted.d),'coefficient ledger')
        require(wanted.certificate()['degree']==4 and packet['degree']==4,'exact degree4')
        leading=list(ZERO);leading[NAMES.index('n' if idx==0 else 'x3')]=4
        require(wanted.d.get(tuple(leading))==1,'uniform degree witness coefficient1')
        report.append(dict(mode=mode,M=cost[0],A=cost[1],witnesses=len(witnesses),
                           polynomial=wanted.certificate(),residuals=len(expected_res)))
        full.append(wanted)
    require(full[1]==full[2],'two independent three-witness schedules')
    boolean=(variable('x2')-variable('x1')-1)*(variable('x2')-variable('x1')-2)
    require(full[4]-full[5]==boolean*boolean-boolean,'unsquared integer Boolean correction')
    return report

def finite_checks(forms,original):
    charts=0;zeros=0
    for x in (0,1,3,8,31):
        times=[]
        for n in range(8):
            h=x+n+1;clock=n*(n+2*x+3)
            for e in (0,1):
                for j in range(h+1):
                    values=dict(x=x,t=clock+j+e*(h+1),x0=0,
                     x1=3+j+e*(h-1-2*j),x2=4+j+e*(h-2*j),
                     x3=x+7+n+e,e=e,n=n,j=j,u=h-j)
                    require(values['x0']<values['x1']<values['x2']<values['x3'],'sorted state')
                    require(all(z==0 for z in source_reference(original,values)),'independent source zero')
                    times.append(values['t']);charts+=1
                    for record in forms:
                        p=record['packet'];env,_=evaluate(p,{k:values[k] for k in p['inputs']+p['witnesses']})
                        require(env[p['output']]==0,'whole saved-array zero');zeros+=1
        require(times==list(range(8*(8+2*x+3))),'half-open charts contiguous and disjoint')
    rational=0
    for case in range(31):
        for idx,record in enumerate(forms):
            p=record['packet'];values={name:Fraction((case+1)*(k+5)%23-11,k%5+1) for k,name in enumerate(p['inputs']+p['witnesses'])}
            env,_=evaluate(p,values);mapped=dict(values)
            if idx>=3:mapped['e']=values['x2']-values['x1']-1
            if idx>=1:mapped['n']=values['x3']-values['x']-7-mapped['e']
            rs=source_reference(original,mapped);wanted=sum(r*r for r in rs)
            if idx>=4:wanted-=rs[4]*rs[4]
            if idx==5:wanted+=rs[0]-rs[0]*rs[0]
            require(env[p['output']]==wanted,'rational full correction');rational+=1
    negative=0
    for x in range(41):
        for n in range(-x-1,0):
            for e in (0,1):
                for j in range(x+n+2):
                    t=n*(n+2*x+3)+j+e*(x+n+2)
                    upper=(n+1)*(n+2*x+4)-1
                    require(t<=upper<0,'negative inverse cycle cannot have natural time');negative+=1
    negative_time=dict(x=0,t=-1,x0=0,x1=2,x2=4,x3=7,e=1,j=0,u=0)
    for record in forms[1:]:
        p=record['packet'];env,_=evaluate(p,{k:negative_time[k] for k in p['inputs']+p['witnesses']})
        require(env[p['output']]==0,'excluded negative time zero')
    real_external=dict(x=0,t=1,x0=Fraction(1,2),x1=3,x2=Fraction(9,2),x3=Fraction(15,2),j=0,u=1)
    outputs=[]
    for record in forms[-2:]:
        p=record['packet'];env,_=evaluate(p,real_external);outputs.append(env[p['output']])
    require(outputs==[Fraction(5,16),0],'integer-external restriction for Boolean fold')
    booleans=[e*(e-1) for e in range(-100,102)]
    require(all(b>=0 for b in booleans) and [e for e in range(-100,102) if e*(e-1)==0]==[0,1],'integer Boolean positivity')
    return dict(chart_states=charts,full_zero_evaluations=zeros,rational_corrections=rational,
      negative_cycle_phase_cases=negative,negative_time_boundary=negative_time,
      real_external_boundary={k:str(v) for k,v in real_external.items()},real_external_outputs=['5/16','0'])

def verify(repo,author):
    for name,pin in DEPENDENCIES.items():require(digest((repo/name).read_bytes())==pin,'frozen dependency '+name)
    require(len(AUTHOR_PINS)==3,'final author pins required')
    for name,pin in AUTHOR_PINS.items():require(digest((author/name).read_bytes())==pin,'author pin '+name)
    data=read_json(author/'timed_binary_shuttle18_projection.json')
    require(data['source_sha256']==AUTHOR_PINS['timed_binary_shuttle18_projection.py'],'source receipt binding')
    require(data['pins']==DEPENDENCIES,'exact predecessor pins')
    original=(repo/(BASE+'code/18-timed-quartics-compact_binary_quartic.py')).read_text()
    report=audit_forms(data['forms'],original);tests=finite_checks(data['forms'],original)
    require(data['full_source_gates']==sum(m+a for m,a in COSTS),'aggregate live gates')
    return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,
      dependencies=DEPENDENCIES,forms=report,total_live_gates=sum(m+a for m,a in COSTS),checks=tests,
      scope='Independent full six-array coefficient/count/domain-boundary audit; fixed binary timed orbit only, no universal bound or generic compiler certification.')

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo-root',required=True,type=Path);p.add_argument('--author-root',required=True,type=Path)
    q=p.add_mutually_exclusive_group(required=True);q.add_argument('--output',type=Path);q.add_argument('--expect',type=Path)
    a=p.parse_args();out=verify(a.repo_root,a.author_root)
    if a.expect:require(same(out,read_json(a.expect)),'type-exact receipt')
    else:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',forms=len(out['forms']),live_gates=out['total_live_gates'],checks=out['checks'])))
if __name__=='__main__':main()
