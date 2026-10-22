#!/usr/bin/env python3
"""Explicit 32-positive-variable quartic construction; finite algebra audit.

This does not verify the imported Pell/compiler lemmas or machine endpoint.
"""
import json
from pathlib import Path
from sparse_polynomial import Ring
from build_systems import COEFFICIENT_BINDING

BASE = 'J F alpha z f h i o j s w tau eta zeta y gamma'.split()
REGISTERS = 'N E P c a X D C2 G L F2 V g I Baux Delta'.split()
NAMES = BASE + REGISTERS
ring = Ring(NAMES+['beta','K0','MC','MF'])
v = ring.variables
globals().update(v)
q = beta*J+1
k = eta+zeta
H = 4*a+3
C = q-F-alpha

equations = [
 ('L = q^2-1', L, q**2-1),
 ('N = q(L+1)', N, q*(L+1)),
 ('X = wq', X, w*q),
 ('a = E+sN', a, E+s*N),
 ('E = X(a-E)', E, X*(a-E)),
 ('c = k(a-E)+eta', c, k*(a-E)+eta),
 ('P = E(c-eta)+k', P, E*(c-eta)+k),
 ('tau^2 = P(P-k)+1', tau**2, P*(P-k)+1),
 ('D = X+ac+gamma(4a+3)', D, X+a*c+gamma*H),
 ('Delta = a^2+4a+3', Delta, a*a+H),
 ('C2 = c^2', C2, c*c),
 ('D^2 = Delta C2+1', D*D, Delta*C2+1),
 ('k = jc-V+1+hE', k, j*c-V+1+h*E),
 ('G = (q-1)(q-F)+alpha', G, (q-1)*(q-F)+alpha),
 ('jc-V = LG+(MC+q MF)J', j*c-V, L*G+(MC+q*MF)*J),
 ('(K0+w)C+(q-F)-z(q-1) = 1', (K0+w)*C+(q-F)-z*(q-1), 1),
 ('F2 = f^2', F2, f*f),
 ('V = of-c', V, o*f-c),
 ('g = y^2-V^2', g, y*y-V*V),
 ('I = i C2', I, i*C2),
 ('Baux = I^2', Baux, I*I),
 ('Baux = Delta(F2-1)', Baux, Delta*(F2-1)),
 ('y^2-Baux g = 1', y*y-Baux*g, 1),
]

residuals = [lhs-rhs for _, lhs, rhs in equations]
degrees = [r.degree(len(NAMES)) for r in residuals]
assert len(NAMES) == len(set(NAMES)) == 32
assert len(equations) == 23
assert set(degrees) == {2}
assert all(('tau' in r.free_variables()) == (index == 7) for index, r in enumerate(residuals))
assert residuals[7].coefficient({'tau':2}) == 1
assert set().union(*(r.free_variables() for r in residuals)) == set(ring.names)

# Every quadratic register is the indicated expression on a source solution.
q0 = beta*J+1
k0 = eta+zeta
X0 = w*q0
Y0 = s*q0**3
E0 = X0*Y0
c0 = k0*Y0+eta
a0 = E0+Y0
H0 = 4*a0+3
Delta0 = a0*a0+H0
D0 = X0+a0*c0+gamma*H0
G0 = (q0-1)*(q0-F)+alpha
R0 = G0*(q0*q0-1)+(MC+q0*MF)*J
V0 = o*f-c0
I0 = i*c0*c0
Baux0 = I0*I0
register_map = {
 'N':q0**3,'E':E0,'P':E0*(c0-eta)+k0,'c':c0,'a':a0,'X':X0,'D':D0,
 'C2':c0*c0,'G':G0,'L':q0*q0-1,'F2':f*f,'V':V0,'g':y*y-V0*V0,
 'I':I0,'Baux':Baux0,'Delta':Delta0,
}

# These are the seven source residuals, with the retained auxiliary coefficient
# I^2. The comparison I^2=Delta(f^2-1) allows either coefficient in that norm.
source_residuals = [
 tau*tau-E0*(k0*Y0)*(E0*(k0*Y0)+k0)-1,
 D0*D0-Delta0*c0*c0-1,
 Baux0*(V0*V0-y*y)+y*y-1,
 k0-h*E0-R0-1,
 (K0+w)*(q0-F-alpha)+(q0-F)-z*(q0-1)-1,
 Baux0-Delta0*(f*f-1),
 j*c0-R0-V0,
]

algebra_checks = []
trivial_indices = {0,1,2,3,4,5,6,8,9,10,13,16,17,18,19,20}
for index, r in enumerate(residuals):
 mapped = r.substitute(register_map)
 expected = {
 7:source_residuals[0],11:source_residuals[1],
 12:source_residuals[3]-source_residuals[6],
 14:source_residuals[6],15:source_residuals[4],
 21:source_residuals[5],22:source_residuals[2],
 }.get(index,ring.coerce(0))
 assert index in trivial_indices or index in {7,11,12,14,15,21,22}
 assert mapped-expected == 0, index
 algebra_checks.append({'residual':index+1,'identity':'passed'})

def polynomial_terms(expr):
 return expr.json_terms()

packet = {
 'name':'inputless-ordinary-retained-quartic32',
 'source_commit':'3b201cdea32d2c816f5f3d20734051f25fd3ef14',
 'domain':'strictly positive integers',
 'constants':['beta','K0','MC','MF'],
 'constant_recipe':'The four-port arithmetic interface is inherited from 06-blank67. The default final binding is ../COEFFICIENT_BINDINGS.json, selecting compiler/tshape_constants.json from the package root, with MF shifted.',
 'coefficient_binding':COEFFICIENT_BINDING,
 'variables':NAMES,
 'sparse_term_coordinate_order':list(ring.names),
 'affine_abbreviations':{'q':'beta*J+1','k':'eta+zeta','H':'4*a+3','C':'q-F-alpha'},
 'equations':[{'number':n+1,'equation':label,'residual':str(r),
               'degree':degrees[n],'terms':polynomial_terms(r)}
              for n,((label,_,_),r) in enumerate(zip(equations,residuals))],
 'single_polynomial':'sum of the squares of the 23 listed residuals',
 'quartic_degree_certificate':'Only residual 8 uses tau, with coefficient +1 on tau^2. The coefficient of tau^4 in the sum of squares is 1.',
 'normalization_to_nonnegative':'replace each of the 32 variables by n+1',
 'formal_status':'Mathematical proof using inherited Pell/compiler theorems; finite symbolic audit only; not kernel checked.',
}

if __name__ == '__main__':
 out=Path(__file__).resolve().parent
 (out/'quartic32.json').write_text(json.dumps(packet,indent=2)+'\n')
 receipt={
  'coefficient_binding':COEFFICIENT_BINDING,
  'positive_variables':len(NAMES),'equations':len(equations),
  'residual_degrees':degrees,'sum_of_squares_degree':4,
  'tau4_coefficient':1,'source_projection_identities':algebra_checks,
  'checks_are_not':['a proof of Con(ZFC)','a Lean/Rocq build','a verification of all imported number theory'],
 }
 (out/'quartic32_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
