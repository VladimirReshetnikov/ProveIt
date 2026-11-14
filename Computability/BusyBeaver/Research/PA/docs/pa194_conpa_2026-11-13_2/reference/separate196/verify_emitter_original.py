"""Independent free-algebra audit of both 196-state numerical AX emitters.

No numeric sampling is used. Constructor terms compare structurally. The
mathematical proofs still rely on upstream arithmetic-macro contracts.
"""
import json,re
from pathlib import Path
import compiler as c
P=Path(__file__).resolve().parent
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
NAMES={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA','node65':'cons','node72':'readH','node75':'readDCons','node142':'copyGuard','node150':'compareGuard',INC:'incT',BREAK:'close'}
ZERO=('zero',);ONE=('succ',ZERO)
def succ(x):return ('succ',x)
def add(x,y):return ('add',x,y)
def I(a,b):return ('im',a,b)
def M(a,b):return succ(I(a,b))
def U(a,b):return succ(succ(I(b,a)))
def E(a,b):return succ(succ(succ(I(a,b))))
def N(a):return I(a,ONE)
def And(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))
def require(v,msg):
 if not v:raise ValueError(msg)
def word(t):
 if t=='node60':return['incT']*2
 if t=='node61':return['incT']*4
 if c.isnode(t):return word(t[0])+word(t[1])
 return[NAMES[t]]
def literal_blocks():
 text=(P/'reference/PA196/Source/AXProgram.lean').read_text().split('def program')[0]
 return[(op,int(a),int(b))for op,a,b in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',text)]
def audit(name):
 t=c.read_grammar(P/name/'grammar.json');ww=word(t);old=[x[0]for x in literal_blocks()]
 require(len(old)==201,'upstream token count')
 expected=old[:121]+['copyA','copyA','copyA','cons','incT','incT','cons']+old[138:]
 if name=='separate196':
  require(expected[184]=='cons','separation edit is the outer constructor');expected=expected[:184]+expected[185:]
 require(ww==expected,'exact modified token word')
 oldt,A,d,h,Y,X=map(lambda z:('atom',z),['t','a','d','h','y','x'])
 T=oldt;D=d;H=h;stack=[];fields=[Y,X]
 for op in ww[:-3]:
  if op=='push':stack.append(T);T=ZERO
  elif op in('copyD','copyH','copyA'):stack.append(T);T={'copyD':D,'copyH':H,'copyA':A}[op]
  elif op=='cons':T=I(stack.pop(),T)
  elif op=='incT':T=succ(T)
  elif op=='readH':H=add(H,fields.pop(0))
  elif op=='readDCons':D=add(D,fields.pop(0));T=I(T,D)
  else:raise ValueError(op)
 require(not fields,'both argument reads')
 heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
 rho=I(I(I(H,d),D),I(I(D,H),I(A,H)))
 gamma=I(A,U(A,A));v=I(M(H,D),U(A,M(H,D)));point=I(A,M(A,D));S=U(D,And(I(M(H,D),point),I(M(A,D),A)));Q=U(A,I(S,N(point)))
 expected_stack=[oldt,U(d,h),rho]+heads
 if name=='diagonal196':expected_top=N(I(gamma,I(v,Q)))
 else:expected_stack.append(gamma);expected_top=N(I(v,Q))
 require(T==expected_top,'full top formula tree');require(stack==expected_stack,'complete formula stack');require(ww[-3:]==['copyGuard','compareGuard','close'],'unchanged final guard and cleanup')
 return {'macro_tokens':len(ww),'pushed_items':len(stack),'free_algebra_exact':True,'guard':'unchanged: output zero if A=D or A=H; then clear A,D,H'}
if __name__=='__main__':
 for name in('diagonal196','separate196'):print(name,json.dumps(audit(name),sort_keys=True))
