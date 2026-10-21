"""Mutation checks for owned balanced-normalized composition checker."""
if not __debug__:
    raise RuntimeError('Assertions required; do not run optimized Python.')
import copy,json,importlib.util,contextlib,io
from pathlib import Path
B=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('owned_combined',B/'check_combined.py')
m=importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):spec.loader.exec_module(m)
results=[]
def reject(name,fn):
    try:fn()
    except (AssertionError,ValueError,IndexError):results.append({'mutation':name,'rejected':True});return
    raise AssertionError('Mutation accepted: '+name)
t=copy.deepcopy(m.tree);t[1]+=1
reject('incorrect left subtree size',lambda:m.flatten(t))
t=copy.deepcopy(m.tree)
v=t
while v[0]=='node':v=v[2]
v[1]=len(m.C)
reject('invalid certificate leaf index',lambda:m.lookup(t,0))
reject('invalid successor index',lambda:m.branch('','',len(m.C)))
reject('wrong initialization successor',lambda:m.branch('','',len(m.C)-1))
assert m.result['literal_endpoint_comparisons_failing']>0
out={'mutations':results,'trailing_zero_equivalence_required':True,
     'literal_endpoint_comparisons_failing':m.result['literal_endpoint_comparisons_failing']}
(B/'MUTATION_CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
