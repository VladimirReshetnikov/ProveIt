#!/usr/bin/env python3
"""Generate a primitive-rule proof DAG by instantiating the frozen generic templates.

The independent checker verify_primitive.py does not parse or trust these templates.
It checks only rho8, modus ponens, generalization and one exact head5 instance.
"""
from pathlib import Path
import re,json,functools,hashlib
if not __debug__:
    raise RuntimeError('Run with assertions enabled; do not use Python -O.')
HERE=Path(__file__).resolve().parent
terms=[['nat',0],['nat',1]];intern={tuple(x):i for i,x in enumerate(terms)}
proofs=[];proved={}
def term(kind,a,b):
    if kind=='I' and a==b==0:return 0
    key=(kind,a,b)
    if key not in intern:intern[key]=len(terms);terms.append(list(key))
    return intern[key]
def I(a,b):return term('I',a,b)
def U(a,b):return term('U',a,b)
def R(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def add(rule,args,conclusion):
    if conclusion not in proved:
        proved[conclusion]=len(proofs)
        proofs.append(dict(rule=rule,args=list(args),conclusion=conclusion))
    return proved[conclusion]
def mp(major,minor):
    p=proofs[major]['conclusion'];q=proofs[minor]['conclusion']
    if p==0:
        assert q==0
        out=0
    else:
        assert terms[p][0]=='I',('major not implication',p)
        _,left,out=terms[p]
        assert left==q,('MP premise mismatch',p,q,left)
    return add('mp',(major,minor),out)

source=(HERE/'reference/RestrictedImplication.lean').read_text()
clean=re.sub(r'/\-.*?\-/','',source,flags=re.S)
pattern=re.compile(r'(?m)^(?:private )?def (\w+) (.*?):=\n',re.S)
ms=list(pattern.finditer(clean));definitions={}
for k,m in enumerate(ms):
    name,signature=m.group(1),m.group(2)
    if name in ('liftRight','rho8All'):continue
    params=[]
    for group in re.findall(r'\(([a-z ]+) : A\)',signature):params.extend(group.split())
    expected=signature.split('Proof ',1)[1].strip()
    body=clean[m.end():ms[k+1].start() if k+1<len(ms)else len(clean)].strip()
    definitions[name]=(params,'(h1 :'in signature,expected,body)

def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|⟹|[()]',s)
class Parser:
    def __init__(self,text,env):self.ts=tokens(text);self.i=0;self.env=env
    def peek(self):return self.ts[self.i]if self.i<len(self.ts)else None
    def take(self,want=None):
        val=self.peek();assert val is not None,('unexpected end',want,self.ts)
        self.i+=1
        if want is not None:assert val==want,(val,want,self.ts)
        return val
    def atom(self):
        if self.peek()=='(':
            self.take('(');out=self.expression();self.take(')');return out
        return self.env[self.take()]
    def expression(self):
        left=self.atom()
        if self.peek()=='⟹':self.take('⟹');return I(left,self.expression())
        return left
    def skip_evidence(self):
        if self.peek()!='(':self.take();return
        depth=0
        while True:
            item=self.take()
            if item=='(':depth+=1
            elif item==')':
                depth-=1
                if depth==0:return
    def proof(self):
        if self.peek()=='(':
            self.take('(');out=self.proof();self.take(')');return out
        name=self.take()
        if name=='rules.mp':return mp(self.proof(),self.proof())
        if name=='rules.row':
            args=[self.atom()for _ in range(4)];self.skip_evidence()
            return add('rho8',args,R(*args))
        assert name in definitions,name
        self.take('rules')
        params,bound,_,_=definitions[name]
        args=tuple(self.atom()for _ in params)
        if bound:self.skip_evidence()
        return instantiate(name,args)
@functools.lru_cache(None)
def instantiate(name,args):
    params,bound,expected,body=definitions[name]
    assert len(params)==len(args)
    env=dict(zip(params,args))
    parser=Parser(body,env);out=parser.proof()
    assert parser.i==len(parser.ts),(name,parser.ts[parser.i:])
    ep=Parser(expected,env);formula=ep.expression()
    assert ep.i==len(ep.ts)
    assert proofs[out]['conclusion']==formula,('wrong template conclusion',name)
    return out

truth=add('rho8',(0,0,0,0),0)
a=I(0,1);aa=I(a,a)
p=instantiate('k',(a,aa));q=instantiate('k',(a,a))
r=instantiate('s',(a,aa,a));identity=mp(mp(r,p),q)
a_truth=mp(instantiate('k',(0,a)),truth)
neg_a=mp(mp(instantiate('s',(a,0,1)),identity),a_truth)
assert proofs[neg_a]['conclusion']==I(a,1)
universal=add('gen',(0,neg_a),U(0,I(a,1)))
h5=add('head5_0_1',(),I(U(0,I(a,1)),1))
final=mp(h5,universal);assert proofs[final]['conclusion']==1
# Keep only proof ancestors of the final contradiction and their term DAG.
needed_proofs=set();todo=[final]
while todo:
    i=todo.pop()
    if i in needed_proofs:continue
    needed_proofs.add(i);line=proofs[i]
    if line['rule']=='mp':todo.extend(line['args'])
    elif line['rule']=='gen':todo.append(line['args'][1])
needed_terms={0,1};todo=[]
for i in needed_proofs:
    line=proofs[i];todo.append(line['conclusion'])
    if line['rule']=='rho8':todo.extend(line['args'])
    elif line['rule']=='gen':todo.append(line['args'][0])
while todo:
    i=todo.pop()
    if i in needed_terms:continue
    needed_terms.add(i)
    if terms[i][0]!='nat':todo.extend(terms[i][1:])
pt={old:new for new,old in enumerate(sorted(needed_proofs))}
tt={old:new for new,old in enumerate(sorted(needed_terms))}
new_proofs=[]
for old in sorted(needed_proofs):
    line=proofs[old];rule=line['rule'];args=line['args']
    if rule=='rho8':args=[tt[x]for x in args]
    elif rule=='mp':args=[pt[x]for x in args]
    elif rule=='gen':args=[tt[args[0]],pt[args[1]]]
    new_proofs.append(dict(rule=rule,args=args,conclusion=tt[line['conclusion']]))
terms=[node if node[0]=='nat' else[node[0],tt[node[1]],tt[node[2]]]
       for old,node in enumerate(terms)if old in needed_terms]
proofs=new_proofs;final=pt[final]
certificate=dict(format='numeric-term-dag-v1',terms=terms,proofs=proofs,final=final,
 source_sha256=hashlib.sha256(source.encode()).hexdigest(),
 term_meanings={'nat':'literal 0 or 1','I':'3*Cantor(a,b)','U':'3*Cantor(body,binder)+2'},
 normalization='I(0,0)=0 only')
(HERE/'primitive_proof.json').write_text(json.dumps(certificate,separators=(',',':'))+'\n')
print(json.dumps(dict(terms=len(terms),proof_steps=len(proofs),final=final,conclusion=1),indent=2))
