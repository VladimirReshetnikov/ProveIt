"""Finite amplitude/cumulant saddle correction, exact with Fraction inputs.
For real amplitude derivatives P[ell], cumulants b[k], standard contour signs.
"""
from math import factorial,comb
from fractions import Fraction

def exact_jet(values):
 out=[]
 for value in values:
  if type(value) not in (int,Fraction):raise TypeError("jets require integer or Fraction values")
  out.append(Fraction(value))
 return out

def doublefact(n):
 out=1
 while n>0:out*=n;n-=2
 return out

def correction(r,P,b):
 if type(r) is not int or r<0:raise ValueError('nonnegative integer order required')
 if len(P)<2*r+1 or len(b)<2*r+3:raise ValueError('insufficient derivative jets')
 P=exact_jet(P);b=exact_jet(b)
 if b[2]<=0:raise ValueError('positive Gaussian variance required')
 total=Fraction(0)
 for ell in range(2*r+1):
  target=2*r-ell
  def walk(k,left,ms):
   nonlocal total
   if k==2*r+3:
    if left:return
    D=ell+sum(j*m for j,m in ms.items());num=(-1)**(ell+r+sum(ms.values()))*doublefact(D-1)*P[ell]
    den=factorial(ell)*b[2]**(D//2)
    for j,m in ms.items():num*=b[j]**m;den*=factorial(j)**m*factorial(m)
    total+=num/den;return
   for m in range(left//(k-2)+1):
    ms[k]=m;walk(k+1,left-(k-2)*m,ms)
   del ms[k]
  walk(3,target,{})
 return total

if __name__=='__main__':
 from fractions import Fraction as F
 import json
 rows=[]
 for j in range(1,8):
  P=[F(2),F(-j,3),F(j+1,5),F(-j,7),F(j+2,11),F(-j,13),F(j+1,17)]
  b=[F(0),F(3),F(j+3),F(j+4),F(j+5),F(j+6),F(j+7),F(j+8),F(j+9)]
  c1=P[0]*(b[4]/(8*b[2]**2)-5*b[3]**2/(24*b[2]**3))-P[1]*b[3]/(2*b[2]**2)-P[2]/(2*b[2])
  vals=[correction(r,P,b) for r in range(4)]
  if vals[1]!=c1:raise RuntimeError('C1 mismatch')
  rows.append(list(map(str,vals)))
 print(json.dumps({'status':'PASS','exact_C1_cases':len(rows),'higher_orders_not_independently_checked':True,'rows':rows},indent=2))
