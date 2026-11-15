#!/usr/bin/env python3
"""Expand the inherited generic rho8All proof for u=7>D=3 at coefficient 3.
A separate checker validates the primitive-rule DAG and structural bounds.
The parsing scaffold is adapted, with attribution, from ProveIt's
pa194nq_research_2026-11-13/search/factor3_obstruction/expand_basis.py.
"""
from pathlib import Path
import re,json,functools,hashlib,gzip,sys
if not __debug__:raise RuntimeError('Use Python without -O')
HERE=Path(__file__).resolve().parent
SYMBOLIC = '--symbolic' in sys.argv
terms=([['var',name] for name in ('D','A','H','u')] if SYMBOLIC
       else [['nat',0],['nat',1],['nat',3],['nat',7]])
intern={tuple(x):i for i,x in enumerate(terms)};proofs=[];proved={}
def term(kind,a,b):
    if not SYMBOLIC and kind=='I' and a==b==0:return 0
    key=(kind,a,b)
    if key not in intern:intern[key]=len(terms);terms.append(list(key))
    return intern[key]
def I(a,b):return term('I',a,b)
def R(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def add(rule,args,conclusion):
    if conclusion not in proved:
        proved[conclusion]=len(proofs)
        proofs.append(dict(rule=rule,args=list(args),conclusion=conclusion))
    return proved[conclusion]
def mp(major,minor):
    p=proofs[major]['conclusion'];q=proofs[minor]['conclusion']
    if not SYMBOLIC and p==0:
        assert q==0
        out=0
    else:
        assert terms[p][0]=='I'
        _,left,out=terms[p];assert left==q,(major,minor,left,q)
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
        val=self.peek();assert val is not None
        self.i+=1
        if want is not None:assert val==want,(val,want)
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
        self.take('rules');params,bound,_,_=definitions[name]
        args=tuple(self.atom()for _ in params)
        if bound:self.skip_evidence()
        return instantiate(name,args)
@functools.lru_cache(None)
def instantiate(name,args):
    params,bound,expected,body=definitions[name];assert len(params)==len(args)
    env=dict(zip(params,args));parser=Parser(body,env);out=parser.proof()
    assert parser.i==len(parser.ts)
    ep=Parser(expected,env);formula=ep.expression();assert ep.i==len(ep.ts)
    assert proofs[out]['conclusion']==formula
    return out

def lift_right(proof,x):
    major=proofs[proof]['conclusion']
    a,b=(0,0) if not SYMBOLIC and major==0 else terms[major][1:]
    swap=mp(instantiate('exchange',(I(x,a),I(a,b),I(x,b))),
            instantiate('composition',(x,a,b)))
    return mp(swap,proof)

def rho_all(a,b,c,u):
    finish=mp(mp(instantiate('composition',(I(I(c,u),c),c,I(b,c))),
                 instantiate('peirce',(c,u))),instantiate('k',(c,b)))
    lifted=lift_right(lift_right(finish,I(a,c)),I(I(c,u),a))
    return mp(lifted,instantiate('composition',(I(c,u),a,c)))

# Nat literal IDs: 2 means 3 and 3 means 7.
parameters=(0,1,2,3) if SYMBOLIC else (2,0,0,3)
final=rho_all(*parameters)
assert proofs[final]['conclusion']==R(*parameters)
needed_proofs=set();todo=[final]
while todo:
    i=todo.pop()
    if i in needed_proofs:continue
    needed_proofs.add(i)
    if proofs[i]['rule']=='mp':todo.extend(proofs[i]['args'])
needed_terms={0,1,2,3};todo=[]
for i in needed_proofs:
    l=proofs[i];todo.append(l['conclusion'])
    if l['rule']=='rho8':todo.extend(l['args'])
while todo:
    i=todo.pop()
    if i in needed_terms:continue
    needed_terms.add(i)
    if terms[i][0]=='I':todo.extend(terms[i][1:])
pt={old:new for new,old in enumerate(sorted(needed_proofs))}
tt={old:new for new,old in enumerate(sorted(needed_terms))}
outproofs=[]
for old in sorted(needed_proofs):
    l=proofs[old];rule=l['rule'];args=l['args']
    args=[tt[x]for x in args] if rule=='rho8' else [pt[x]for x in args]
    outproofs.append(dict(rule=rule,args=args,conclusion=tt[l['conclusion']]))
outterms=[node if node[0] in ('nat','var') else ['I',tt[node[1]],tt[node[2]]]
          for old,node in enumerate(terms) if old in needed_terms]
cert=dict(format=('generic-rho8all-template-v1' if SYMBOLIC else 'tagged3-rho8all-example-v1'),
          coefficient=('arbitrary implication dominating both arguments' if SYMBOLIC else 3),
          terms=outterms,proofs=outproofs,final=pt[final],
          parameters=({'D':'D','A':'A','H':'H','u':'u'} if SYMBOLIC else {'D':3,'A':0,'H':0,'u':7}),
          source_sha256=hashlib.sha256(source.encode()).hexdigest(),
          status=('Formal unrestricted rho template expanded to primitive rules' if SYMBOLIC
                  else 'Unrestricted rho instance with numerical u>D, expanded to primitive rules'))
raw=(json.dumps(cert,separators=(',',':'))+'\n').encode()
filename='rho_generic_template.json.gz' if SYMBOLIC else 'rho_guard_certificate.json.gz'
with gzip.GzipFile(filename=str(HERE/filename),mode='wb',mtime=0) as f:f.write(raw)
print(json.dumps({'terms':len(outterms),'proof_rows':len(outproofs),'raw_bytes':len(raw),'final':pt[final]},indent=2))
