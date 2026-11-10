#!/usr/bin/env python3
import ast,hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-seed-readable-prefix-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(root/'equation.tex')=='94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635' and sha(p/'Current14QuotedPrefix.lean')=='a1e2a83f3486ce2af92ce165e72f6889f6e6456a0d14810ecee425d888d2a1d0' and sha(p/'PLAN.md')=='01c0a8a017e6f83181ffea0258806ec91dc802c340cd471e368c89c8c9aadd1e'
tex=(root/'equation.tex').read_text();expected_tex=r'''b=\beta J,\quad q=b+1,\quad C=q-F-\alpha,\\
X=wq,\quad Y=sq^3,\quad E=XY,\quad k=\eta+\zeta,\\
\ell=EkY,\quad c=kY+\eta,\quad a=E+Y,\\
H=4a+3,\quad\Delta=a^2+H,\quad D=X+ac+\gamma H,\\
R=[b(q-F)+\alpha](q^2-1)+(\mu+q\omega)J,\\
\tau=En+k-R,\quad V=f^2(cT-R)-c,\\
P=\tau^2-\ell(\ell+k),\quad Q=D^2-\Delta c^2,\\
S=i\Delta c^2,\quad U=S^2(V^2-y^2)+y^2,\\
W=(K+w)C+(q-F)-zb,\quad Z=\Delta f^2-S^2.''';assert expected_tex in tex and r'\boxed{PQUWZ-\Delta=0.}' in tex and r'J,F,\alpha,z,f,i,T,s,w,n,\eta,\zeta,y,\gamma\in\mathbb Z_{>0}' in tex
s=(p/'Current14QuotedPrefix.lean').read_text();m=re.search(r'def quoted : List \(List String\) := (\[.*?\]\])\s*\n\ndef quotedExpr',s,re.S);assert m;lines=ast.literal_eval(m.group(1));assert len(lines)==23
V=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'];P=['beta','K','mu','omega'];assert re.findall(r'\("([A-Za-z]+)", \.var (\d+)\)',s)==list(zip(V,map(str,range(14)))) and re.findall(r'\("(beta|K|mu|omega)", \.constant \(p (\d)\)\)',s)==list(zip(P,map(str,range(4))))
# Independently specify the page's infix grouping as prefix-expression trees.
a=lambda x,y:('+',x,y);d=lambda x,y:('-',x,y);m0=lambda x,y:('*',x,y);sq=lambda x:('sq',x);cu=lambda x:('cube',x)
expected=[('b',m0('beta','J')),('q',a('b','1')),('C',d(d('q','F'),'alpha')),('X',m0('w','q')),('Y',m0('s',cu('q'))),('E',m0('X','Y')),('k',a('eta','zeta')),('ell',m0(m0('E','k'),'Y')),('c',a(m0('k','Y'),'eta')),('a',a('E','Y')),('H',a(m0('4','a'),'3')),('Delta',a(sq('a'),'H')),('D',a(a('X',m0('a','c')),m0('gamma','H'))),('R',a(m0(a(m0('b',d('q','F')),'alpha'),d(sq('q'),'1')),m0(a('mu',m0('q','omega')),'J'))),('tau',d(a(m0('E','n'),'k'),'R')),('V',d(m0(sq('f'),d(m0('c','T'),'R')),'c')),('P',d(sq('tau'),m0('ell',a('ell','k')))),('Q',d(sq('D'),m0('Delta',sq('c')))),('S',m0(m0('i','Delta'),sq('c'))),('U',a(m0(sq('S'),d(sq('V'),sq('y'))),sq('y'))),('W',d(a(m0(a('K','w'),'C'),d('q','F')),m0('z','b'))),('Z',d(m0('Delta',sq('f')),sq('S'))),('result',d(m0(m0(m0(m0('P','Q'),'U'),'W'),'Z'),'Delta'))]
known=set(V+P+['1','2','3','4'])
def read(tokens,fuel):
 if fuel<=0 or not tokens:raise ValueError('fuel or missing')
 head,*tail=tokens
 if head in ('+','-','*'):
  x,tail=read(tail,fuel-1);y,tail=read(tail,fuel-1);return ((head,x,y),tail)
 if head in ('sq','cube'):
  x,tail=read(tail,fuel-1);return ((head,x),tail)
 if head not in known:raise ValueError('unknown')
 return head,tail
for line,(name,tree) in zip(lines,expected):
 assert line[:2]==[name,'='] and name not in known;actual,remain=read(line[2:],64);assert actual==tree and not remain,(name,actual,tree,remain);known.add(name)
assert len({x[0] for x in lines})==23
# Direct source inspection: lhs accepts arbitrary fresh strings; not validated as identifiers.
assert '| name :: "=" :: tokens => do' in s and 'if (lookup name env).isSome then none else' in s and 'if rest.isEmpty then some ((name, value) :: env) else none' in s
assert '+' not in set(V+P+['1','2','3','4']) and '' not in set(V+P+['1','2','3','4'])
for bad in (['+','ghost'],['+','1'],['1','2']):
 try:
  _,rem=read(bad,64)
  if bad==['1','2']:assert rem
  else:assert False
 except ValueError:pass
print(json.dumps({'status':'PASS_TRANSCRIPTION_WITH_GRAMMAR_FINDING','tex_named_definitions':22,'final_expression':1,'variables':14,'ports':4,'finding':'step does not validate declaration identifiers; fresh empty/reserved operator names accepted, so blanket malformed-declaration rejection is too broad','scope':'manual TeX-source transcription review and Python structural audit, no Lean/PDF bytes theorem'},indent=2))
