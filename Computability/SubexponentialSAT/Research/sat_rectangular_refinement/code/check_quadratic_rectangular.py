#!/usr/bin/env python3
"""Exact rational checks of a local lemma; not a SAT solver or matrix backend."""
from fractions import Fraction as F
from itertools import combinations
from math import comb,sqrt
from pathlib import Path
import json

def require(condition,message):
 if not condition:raise ValueError(message)

def add(a,b):
 c=[F(0)]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c

def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def scale(a,t):return [t*x for x in a]

def matmul(A,B):
 Bt=list(zip(*B))
 return [[sum(x*y for x,y in zip(row,col)) for col in Bt] for row in A]

def matsub(A,B):return [[x-y for x,y in zip(a,b)] for a,b in zip(A,B)]

def scalarI(n,k):return [[int(i==j)*k for j in range(n)] for i in range(n)]

# Check the discriminant numerator 2304*x^2*(4AC-B^2).
lhs=add(scale([F(-6),0,337,-220,289],289),scale(mul([12,55,103],[12,55,103]),-4))
R=[F(-2310),F(-7590),F(67815),F(-41085)]
rhs=mul([1,-1],R)
require(lhs==rhs,"Discriminant factorization failed")
# Substitute x=(1+t)/2 and convert power coefficients to Bernstein form.
power=[F(0)]*4
for j,coef in enumerate(R):
 for k in range(j+1):power[k]+=coef*F(comb(j,k),2**j)
bern=[sum(power[k]*F(comb(i,k),comb(3,k)) for k in range(i+1)) for i in range(4)]
require(bern==[F(45705,8),F(10615),F(32065,2),F(16830)],"Bernstein expansion failed")
require(all(x>0 for x in bern),"Bernstein positivity failed")
a,b,c=F(1),F(1),F(20,17)
U=c+a+b*b/(4*a)
Q=F(55,96)*(7*(a*a+b*b+c*c)-4*(a*b+a*c+b*c))
require(U*U==Q,"Equality case failed")

# Build the affine supports independently from finite-field coordinates.
edges=list(combinations(range(9),2))
H=[]
for direction in range(4):
 labels=[]
 for point in range(9):
  x,y=divmod(point,3)
  labels.append(x if direction==3 else (y-direction*x)%3)
 for colors in combinations(range(3),2):
  H.append([int(tuple(sorted((labels[x],labels[y])))==colors) for x,y in edges])
Gram=matmul(H,list(zip(*H)))
for i in range(12):
 for j in range(12):
  require(Gram[i][j]==(9*int(i==j) if i//3==j//3 else 2),"Affine support intersection failed")
K=[[((9*int(i==j)-2) if i//3==j//3 else 0) for j in range(12)] for i in range(12)]
Z=matmul(list(zip(*H)),matmul(K,H))
require(Z==list(map(list,zip(*Z))),"Spectral matrix is not symmetric")
# Symmetry and this exact polynomial restrict every eigenvalue to 0,9,81.
poly=matmul(matmul(Z,matsub(Z,scalarI(36,9))),matsub(Z,scalarI(36,81)))
require(all(x==0 for row in poly for x in row),"Spectral annihilating polynomial failed")
trace=sum(Z[i][i] for i in range(36))
Z2=matmul(Z,Z);trace2=sum(Z2[i][i] for i in range(36))
require(trace==756 and trace2==59292,"Spectral trace failed")
require(9*3+81*9==trace and 9**2*3+81**2*9==trace2,"Spectral multiplicity failed")
beta2=F(2,81)*F(55,384)*81
require(beta2==F(55,192),"Coefficient normalization failed")
out={
 'scope':'A final-triangle certificate only. Internal block construction is not included.',
 'quadratic_majorant_coefficient':'55/96',
 'equality_dimensions':['1','1','20/17'],
 'bernstein_coefficients':[str(x) for x in bern],
 'matrix_shape':[36,36],
 'integer_spectral_eigenvalues':{'0':24,'9':3,'81':9},
 'trace':trace,'trace_square':trace2,
 'beta_squared':str(beta2),'beta_decimal':sqrt(beta2),
 'all_exact_checks_passed':True
}
print(json.dumps(out,indent=2))
