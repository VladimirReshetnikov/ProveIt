"""Build an explicit quadratic system / quartic SOS from the 82-gate circuit."""
from pathlib import Path
import json

root=Path(__file__).resolve().parent
p=json.loads((root/'k215_native82_source.json').read_text())
ref={n:['+', ['var', 'x'+str(j+1)], ['int',1]] for j,n in enumerate(p['positive_witnesses'])}
ref.update({n:['coef',n] for n in p['fixed_numerals']})
variables=['x'+str(j+1) for j in range(18)]
residuals=[]
def term(x):return ['int',x] if type(x) is int else ref[x]
for j,(name,op,a,b) in enumerate(p['source'][:-1]):
    value=[op,term(a),term(b)]
    plus,minus=f'z{j+1}_plus',f'z{j+1}_minus'
    variables.extend([plus,minus])
    ref[name]=['-',['var',plus],['var',minus]]
    residuals.append(['-',ref[name],value])
name,op,a,b=p['source'][-1]
assert name==p['output'] and op=='-'
residuals.append(['-',term(a),term(b)])
assert len(variables)==180 and len(residuals)==82
out={'description':'82 quadratic equations in 180 nonnegative integer variables, equivalent to the native18-positive-witness polynomial',
     'coefficient_recipe':'native/k215_native_definition.py:k215_coefficients',
     'fixed_numerals':p['fixed_numerals'], 'variables':variables,'domain':'nonnegative integers',
     'expression_grammar':'[int,n], [var,name], [coef,name], or [op,left,right] with op +,-,*',
     'residuals':residuals,'equations':'Each residual equals zero',
     'single_quartic_equation':'The sum of the squares of the 82 residuals equals zero',
     'maximum_residual_degree':2,'maximum_SOS_degree':4,
     'formal_status':'Elementary circuit-lifting argument; not kernel-checked'}
(root/'quadratic_system.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'variables':len(variables),'equations':len(residuals),'SOS_degree_bound':4}))
