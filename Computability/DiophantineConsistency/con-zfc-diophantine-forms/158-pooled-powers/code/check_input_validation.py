"""Negative controls for strict literal decoding and evaluator inputs."""
from pathlib import Path
import copy,json,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from verify import read,validate_equation,P
from evaluate import evaluate

def must_reject(name,call):
 try:call()
 except ValueError:return name
 raise ValueError('malformed input was accepted: '+name)

def main():
 original=read(ROOT/'stages'/'principal225'/'equation.json');controls=[]
 def mutated(name,fn):
  e=copy.deepcopy(original);fn(e);controls.append(must_reject(name,lambda:validate_equation(e)))
 mutated('duplicate monomial',lambda e:e['residuals'][0]['terms'].append(copy.deepcopy(e['residuals'][0]['terms'][0])))
 mutated('zero coefficient',lambda e:e['residuals'][0]['terms'][0].__setitem__(0,0))
 mutated('Boolean coefficient',lambda e:e['residuals'][0]['terms'][0].__setitem__(0,True))
 mutated('float coefficient',lambda e:e['residuals'][0]['terms'][0].__setitem__(0,1.0))
 mutated('negative coordinate',lambda e:e['residuals'][0]['terms'][0].__setitem__(1,[-1]))
 mutated('out-of-range coordinate',lambda e:e['residuals'][0]['terms'][0].__setitem__(1,[225]))
 mutated('Boolean coordinate',lambda e:e['residuals'][0]['terms'][0].__setitem__(1,[False]))
 mutated('unsorted monomial',lambda e:e['residuals'][0]['terms'][0].__setitem__(1,[2,1]))
 mutated('unsorted term sequence',lambda e:e['residuals'][0]['terms'].reverse())
 mutated('residual degree three',lambda e:e['residuals'][0]['terms'][0].__setitem__(1,[0,0,0]))
 mutated('empty residual',lambda e:e['residuals'][0].__setitem__('terms',[]))
 mutated('unused declared coordinate',lambda e:e['variables'].append({'name':'unused-extra','kind':'unused'}))
 mutated('duplicate coordinate name',lambda e:e['variables'][1].__setitem__('name',e['variables'][0]['name']))
 mutated('incorrect domain',lambda e:e.__setitem__('domain','nonnegative integers'))
 with tempfile.TemporaryDirectory() as td:
  p=Path(td)/'bad.json';p.write_text('{"a":1,"a":2}')
  controls.append(must_reject('duplicate JSON object key',lambda:read(p)))
  p.write_text('{"a":NaN}')
  controls.append(must_reject('nonfinite JSON number',lambda:read(p)))
 zero=[0]*225
 for name,values in [('short tuple',zero[:-1]),('long tuple',zero+[0]),('Boolean tuple entry',[True]+zero[1:]),('float tuple entry',[0.0]+zero[1:]),('numeric string entry',['0']+zero[1:]),('object instead of tuple',{})]:
  controls.append(must_reject(name,lambda values=values:evaluate(original,values)))
 # Compare the evaluator with the separately expanded polynomial at explicit
 # assignments. These are algebraic/evaluator checks, never a root search.
 full=P(read(ROOT/'stages'/'principal225'/'expanded_polynomial.json')['terms'])
 evaluation=[]
 for values in (zero,[1]*225,[(i%7)-3 for i in range(225)]):
  total=0
  for mon,coefficient in full.items():
   term=coefficient
   for i in mon:term*=values[i]
   total+=term
  actual=evaluate(original,values)
  if actual['polynomial_value']!=total:raise ValueError('evaluator differs from full expansion')
  evaluation.append({'polynomial_value':total,'nonzero_residuals':actual['nonzero_residual_count']})
 return {'result':'passed','rejected_malformed_inputs':controls,'negative_control_count':len(controls),'evaluator_expansion_comparisons':evaluation,'distinct_used_coordinates':validate_equation(original)['distinct_used_coordinates']}
if __name__=='__main__':print(json.dumps(main(),indent=2))
