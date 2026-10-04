import hashlib,inspect,itertools,json,pathlib,random,subprocess,sys,os
A=pathlib.Path(os.environ['AUDIT_ROOT']);R=A/'extracted'
sys.path.insert(0,str(R/'atlas'))
from compile_input import compile_input
from generator import Atlas
from physical_program import row_at
sha=lambda b:hashlib.sha256(b).hexdigest()
a=Atlas();raw=(R/'copy/fixed_initial_anchor_patch.json').read_bytes();anchor=json.loads(raw);pin=sha(raw)
assert str(inspect.signature(compile_input))=='(left, right)'
for kw in ['anchor','program','hardware','observer']:
 try:compile_input([],[],**{kw:None})
 except TypeError:pass
 else:raise AssertionError(('accepted unauthorized API parameter',kw))
invalid=[[True],[False],[0.0],[1.0],[-1],[2],['0'],['1'],[None]]
for word in invalid:
 for left,right in [(word,[]),([],word)]:
  try:compile_input(left,right)
  except ValueError:pass
  else:raise AssertionError(('invalid bits accepted',left,right))
words=[list(bits)for n in range(3)for bits in itertools.product([0,1],repeat=n)]
cases=list(itertools.product(words,repeat=2))
for n in [0,1,2,3,4,7,16,31]:cases.extend([([0]*n,[]),([],[0]*n),([0]*n,[0]*n)])
rng=random.Random(4175)
for _ in range(12):cases.append(([rng.randrange(2)for _ in range(rng.randrange(20))],[rng.randrange(2)for _ in range(rng.randrange(20))]))
results=[]
for left,right in cases:
 p=compile_input(left,right);m=len(left)+len(right)+1
 expected={(x,y):new for x,y,old,new in anchor['patch']}
 def set_field(module,slot):
  for delta in [104,105]:expected[576000*module+600+24000*slot+delta,54]=0
 set_field(0,12);set_field(m,11)
 states=left[::-1]+[2]+right
 for i,v in enumerate(states):
  for bit in range(11):
   if(v>>bit)&1:set_field(i,13+bit);set_field(i+1,bit)
 actual={(x,y):c for x,y,c in p['changed_cells']}
 assert len(actual)==len(p['changed_cells'])==2812+4*(sum(left)+sum(right))
 assert actual==expected
 assert p['fixed_initial_head']==[288650,75,1]and p['primary_word_length']==m
 assert p['period']==[576000,481238074400]and p['stencil']==[]
 assert p['pre_departure_acceptance']==[{'x_residue':546702,'y_residue':240606225650,'heading':2},{'x_residue':258702,'y_residue':481225262850,'heading':2}]
 assert min(x for x,y in actual)==288617 and max(x for x,y in actual)==576000*m+264705
 assert min(y for x,y in actual)==-144 and max(y for x,y in actual)==76
 results.append({'left_length':len(left),'right_length':len(right),'popcount':sum(left)+sum(right),'support':len(actual),'expected_map_sha256':sha(json.dumps(p['changed_cells'],separators=(',',':')).encode())})
# Independent arithmetic placement of accepting clauses; then verify their exact local role.
p=a.program;r=p['observer_row_index'];k=p['observer_column_index'];assert row_at(p,r)==('DUP',k)
assert(r,k)==(601515562,910)
base=(600+600*k+102,400+400*r+450,2)
clauses=[(base[0]%a.S,base[1]%(2*a.V),2),((base[0]+a.S//2)%a.S,(base[1]+a.V)%(2*a.V),2)]
assert clauses==[(546702,240606225650,2),(258702,481225262850,2)]
dup=json.loads((R/'copy/pair_dup.json').read_text());observer=[]
for c in dup['cases']:
 pres=[row for tr in c['pre_read_phase_traces']for row in tr if row[:3]==[102,450,2]]
 posts=[row for tr in c['output_read_phase_traces']for row in tr if row[:3]==[102,450,2]]
 assert len(pres)==c['effective_inputs'][0]and not posts
 observer.append({'input_kinds':c['input_kinds'],'left_bit':c['effective_inputs'][0],'accepting_departures':len(pres),'later_read_hits':len(posts)})
# Extra periodicity probes include signed boundaries, enormous coordinates and actual painted cells.
coords=[(0,0),(-1,-1),(-a.S,-2*a.V),(a.S,2*a.V),(base[0],base[1]),(288650,75),(a.right+174,80),(a.right+175,a.F+69)]
for _ in range(64):coords.append((rng.randrange(-10**18,10**18),rng.randrange(-10**18,10**18)))
for x,y in coords:
 c=a.color(x,y);assert c in[0,1]
 assert a.color(x+a.S,y)==c and a.color(x,y+2*a.V)==c and a.color(x-a.S,y-2*a.V)==c
# Repeated calls must not share any mutable output container or caller input list.
left=[1,0,1];right=[0,1,0,1]
one=compile_input(left,right);two=compile_input(left,right)
canonical=json.dumps(one,sort_keys=True);assert json.dumps(two,sort_keys=True)==canonical

def mutable_ids(obj):
 found=set()
 def visit(v):
  if isinstance(v,(list,dict,set,bytearray)):
   assert id(v)not in found,('internal output alias',type(v).__name__)
   found.add(id(v))
   if isinstance(v,dict):
    for z in v.values():visit(z)
   elif isinstance(v,list):
    for z in v:visit(z)
 visit(obj);return found
first_ids=mutable_ids(one);second_ids=mutable_ids(two)
assert not(first_ids&second_ids)
assert not({id(left),id(right)}&(first_ids|second_ids))
# Mutating caller inputs after compilation must not affect either old result.
left.clear();right[:]=[1]*17
assert json.dumps(one,sort_keys=True)==canonical and json.dumps(two,sort_keys=True)==canonical
# Mutate every nested container from leaves upward, including all changed-cell rows.
mutated=0

def destroy(v):
 global mutated
 if isinstance(v,dict):
  for z in list(v.values()):destroy(z)
  v.clear();v['poison']='audit mutation';mutated+=1
 elif isinstance(v,list):
  for z in list(v):destroy(z)
  v[:]=['audit mutation'];mutated+=1

destroy(one)
assert mutated==len(first_ids)
assert json.dumps(two,sort_keys=True)==canonical
three=compile_input([1,0,1],[0,1,0,1]);assert json.dumps(three,sort_keys=True)==canonical
assert three['fixed_initial_head']==[288650,75,1]
# Original minimal reproducer must now leave later metadata untouched.
headtest=compile_input([],[]);headtest['fixed_initial_head'][0]=123
assert compile_input([],[])['fixed_initial_head']==[288650,75,1]
alias={'status':'PASS_NO_MUTABLE_OUTPUT_OR_CALLER_ALIASES','mutable_containers_per_result':len(first_ids),'destructively_mutated_containers':mutated,'later_result_exact_after_mutation':True,'original_head_reproducer_fixed':True}
report={'status':'PASS_HARDENED_INTERFACE_AND_REPEATED_CALL_ISOLATION','valid_input_cases':len(results),'invalid_bit_calls_rejected':2*len(invalid),'unauthorized_parameter_calls_rejected':4,'endpoint_zero_word_lengths':[0,1,2,3,4,7,16,31],'all_maps_independently_reconstructed':True,'periodicity_probe_points':len(coords),'observer_cases':observer,'api_return_isolation':alias,'input_cases':results,'source_sha256':sha(pathlib.Path(__file__).read_bytes())}
(A/'independent_interface_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in['input_cases','observer_cases']}))
