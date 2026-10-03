import sympy as s
from itertools import product
k,N,K,h=s.symbols('k N K h',integer=True,positive=True)
L={a:s.symbols('l'+str(a).replace('-','m')) for a in range(-3,2)}
z=s.symbols('z',nonnegative=True)
# term(u1,u2,E-index offset rel k,L-index offset rel k,zpower,coreedgeflag)
def terms(shift,baseonly=False):
 arr=[((0,0),shift,shift,0,False),((1,0),shift-1,shift-1,0,False),((0,1),shift-1,shift-1,0,False),((1,1),shift-2,shift-2,1,False)]
 if not baseonly:arr +=[((1,0),shift,shift-1,0,True),((0,1),shift,shift-1,0,True),((1,1),shift-1,shift-2,0,True),((1,1),shift,shift-2,0,True)]
 return arr

def raw(lam,d):
 out=0
 for shifts,fac in [((0,0),k*(N-k)),((-1,1),-(k+1)*(N-k+1))]:
  for a,b in product(terms(shifts[0]),terms(shifts[1])):
   if not(a[4]or b[4]):continue
   if tuple(x+y for x,y in zip(a[0],b[0]))!=lam:continue
   if a[1]+b[1]!=-d:continue
   out+=fac*s.Symbol('b'+str(-a[1]).replace('-','m'))*L[a[2]]*L[b[2]]*z**(a[3]+b[3])
 return s.expand(out)

def ratios(d):
 # binom(2K-d,K-j) / central coefficient, valid at sufficiently large integerK
 c=d//2
 rats={}
 for j in range(-1,4):
  ratio=s.S.One
  if j>c:
   for a in range(c,j):ratio*=s.Rational(1)*(K-a)/(K-d+a+1)
  elif j<c:
   for a in range(j,c):ratio*=s.Rational(1)*(K-d+a+1)/(K-a)
  rats[s.Symbol('b'+str(j).replace('-','m'))]=s.factor(ratio)
 return rats
if __name__=='__main__':
 for lam in [(1,0),(2,0),(1,1),(2,1),(2,2)]:
  for d in range(sum(lam)):
   f=raw(lam,d);g=s.factor(f.subs(ratios(d)))
   print(lam,d,'raw',s.factor(f));print('ratio',g)
