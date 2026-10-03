"""Build exact rational example files and basic compiler checks."""
from pathlib import Path
from fractions import Fraction
import json
import sympy as sp
from mixing_compiler import compile_family, separation_horizon

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'examples'
OUT.mkdir(exist_ok=True)
x, y, z = sp.symbols('x y z')
examples = [
    ('difference_square', (x-y)**2-1, (x,y), Fraction(1,2)),
    ('product_graph', x*y-z, (x,y,z), Fraction(1,2)),
    ('radial_quartic', (x*x+y*y)**2, (x,y), Fraction(1,2)),
    ('fast_mixing', (x-y)**2-1, (x,y), Fraction(1,100)),
]
summary=[]
for name,P,vs,theta in examples:
    m=compile_family([P],vs,theta)
    p,eps=m.initial(P)
    assert sp.expand(m.recover_polynomial(P)-eps*P)==0
    m.export(P,OUT/f'{name}.json',name)
    summary.append(dict(name=name,rank=m.rank,states=m.states,q=str(m.q),epsilon=str(eps)))
Q0=z*z+(z-x*y)**2
family=compile_family([Q0,z,sp.Integer(1)],(x,y,z))
w_coeff=[family.coordinates(Q0)*family.E,
         family.coordinates(-2*z)*family.E, family.coordinates(1)*family.E]
C2=1+max(sum(abs(w[j]) for w in w_coeff) for j in range(family.states))
for t in [0,1,2,6,11]:
    Q=sp.expand(Q0-2*t*z+t*t)
    eps=1/(family.states*C2*(1+t)**2)
    family.export(Q,OUT/f'factor_family_{t}.json',f'factor_family_{t}',eps)
    assert sp.expand(family.recover_polynomial(Q,eps)-eps*Q)==0
    summary.append(dict(name=f'factor_family_{t}',rank=family.rank,states=family.states,
                        q=str(family.q),epsilon=str(eps)))
# A genuinely straight-line initial loader at one higher polynomial degree.
P0=-z+(z+1)*(z-x*y)**2
line=compile_family([P0],(x,y,z))
w0=line.coordinates(P0)*line.E
w1=line.coordinates(1)*line.E
C1=1+max(abs(a) for w in [w0,w1] for a in w)
for t in [0,1,2,6,11]:
    P=sp.expand(P0+t)
    eps=1/(line.states*C1*(1+t))
    line.export(P,OUT/f'factor_line_{t}.json',f'factor_line_{t}',eps)
    assert sp.expand(line.recover_polynomial(P,eps)-eps*P)==0
    summary.append(dict(name=f'factor_line_{t}',rank=line.rank,states=line.states,
                        q=str(line.q),epsilon=str(eps)))

# Radial quartics attain the proved sharp rank bound, for these test sizes.
radial=[]
for k in range(1,5):
    vs=sp.symbols(f'u0:{k}')
    P=sum(v*v for v in vs)**2
    m=compile_family([P],vs)
    assert m.states==int(sp.binomial(k+3,2))
    radial.append(dict(variables=k,rank=m.rank,states=m.states))
# Intentional contract failures: no floating-point coefficients/counts.
model=compile_family([(x-y)**2-1],(x,y))
rejected=0
bad_actions=[
    lambda: compile_family([0],(x,)),
    lambda: compile_family([x+sp.Float('0.1')],(x,)),
    lambda: compile_family([x+z],(x,)),
    lambda: compile_family([x],(x,x)),
    lambda: compile_family([x],(x,),0.5),
    lambda: compile_family([x],(x,),True),
    lambda: compile_family([x],(x,),Fraction(0)),
    lambda: compile_family([x],(x,),Fraction(1)),
    lambda: model.acceptance((x-y)**2-1,(-1,0)),
    lambda: model.acceptance((x-y)**2-1,(True,0)),
    lambda: model.acceptance((x-y)**2-1,(1.0,0)),
    lambda: model.acceptance((x-y)**2-1,(0,)),
    lambda: model.initial(x**10),
    lambda: model.initial(x),
    lambda: model.initial((x-y)**2-1,0),
    lambda: model.initial((x-y)**2-1,Fraction(1)),
    lambda: model.initial((x-y)**2-1,0.1),
    lambda: model.initial((x-y)**2-1,True),
    lambda: separation_horizon(Fraction(1,2),0),
]
for action in bad_actions:
    try:
        action()
    except (TypeError,ValueError):
        rejected+=1
    else:
        raise AssertionError('Malformed input was accepted')
assert separation_horizon(Fraction(1,2),Fraction(1,8))==4
report={'example_count':len(summary),'examples':summary,'radial_rank_checks':radial,
        'malformed_inputs_rejected':rejected,'reverse_polynomial_checks':len(summary),
        'quadratic_loader_C':str(C2),'linear_loader_C':str(C1),
        'sympy_version':sp.__version__}
(ROOT/'verification'/'compiler_report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
