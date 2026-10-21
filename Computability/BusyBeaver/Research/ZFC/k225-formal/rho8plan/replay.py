"""Replay an untrusted original-node proof plan without an optimization solver.

The original Source149 certificate is immutable. Planned substitutions and
topological order are checked here; Lean/Rocq still check every emitted proof.
"""
from pathlib import Path
import argparse,copy,hashlib,json

def replay(original,plan):
 assert plan['format']=='original_node_rule_plan_v1'
 assert hashlib.sha256(original).hexdigest()==plan['original_sha256']
 d=json.loads(original);T=d['term_table'];N=d['nodes']
 assert len(T)==plan['original_term_count'] and len(N)==plan['original_node_count']
 assert all(node['id']==i for i,node in enumerate(N))
 order=plan['topological_original_node_ids'];nm={old:new for new,old in enumerate(order)}
 assert len(nm)==len(order)==plan['expected_nodes']
 assert all(isinstance(i,int) and 0<=i<len(N) for i in order)
 assert order[-1]==plan['root_original_id']==d['roots']['rho8']
 zero=next(i for i,t in enumerate(T) if t=='T');keys={}
 for i,t in enumerate(T):
  if isinstance(t,list):assert len(t)==2 and all(0<=j<i for j in t)
  key=('T',) if t=='T' else ('V',t['var']) if isinstance(t,dict) else ('I',*t)
  assert key not in keys;keys[key]=i
 def instantiated(parent,env):
  memo={}
  def go(i):
   if i in memo:return memo[i]
   t=T[i]
   if t=='T':r=zero
   elif isinstance(t,dict):r=env.get(str(t['var']),zero)
   else:
    a,b=go(t[0]),go(t[1]);r=zero if a==b==zero else keys.get(('I',a,b),-1)
   memo[i]=r;return r
  return go(parent)
 assert all(str(int(i))==i and int(i) in nm for i in plan['rule_overrides'])
 rules={};used_terms=set()
 def visit(t):
  assert 0<=t<len(T)
  if t in used_terms:return
  used_terms.add(t)
  if isinstance(T[t],list):
   for j in T[t]:visit(j)
 for old in order:
  rule=copy.deepcopy(plan['rule_overrides'].get(str(old),N[old]['rule']))
  for field in ('parent','major','minor'):
   if field in rule:assert rule[field] in nm and nm[rule[field]]<nm[old]
  if str(old) in plan['rule_overrides']:
   assert rule['kind']=='substitution' and set(rule)=={'kind','parent','substitution'}
   assert all(str(int(v))==v and 0<=t<len(T) for v,t in rule['substitution'].items())
   assert instantiated(N[rule['parent']]['term'],rule['substitution'])==N[old]['term']
  rules[old]=rule;visit(N[old]['term'])
  for field in ('substitution','major_substitution','minor_substitution'):
   for t in rule.get(field,{}).values():visit(t)
 for i,t in enumerate(T):
  if t=='T' or isinstance(t,dict):visit(i)
 terms=sorted(used_terms);tm={old:new for new,old in enumerate(terms)}
 assert len(terms)==plan['expected_terms']
 nodes=[]
 for old in order:
  rule=rules[old]
  for field in ('parent','major','minor'):
   if field in rule:rule[field]=nm[rule[field]]
  for field in ('substitution','major_substitution','minor_substitution'):
   if field in rule:rule[field]={v:tm[t] for v,t in rule[field].items()}
  nodes.append({'id':nm[old],'term':tm[N[old]['term']],'rule':rule,'origin':old})
 assert sum(3 if node['rule']['kind']=='mp_substitution' else 1 for node in nodes)==plan['expected_expanded_instructions']
 d['nodes']=nodes;d['term_table']=[[tm[c] for c in T[t]] if isinstance(T[t],list) else T[t] for t in terms]
 d['roots']={k:nm[v] for k,v in d['roots'].items() if v in nm};d['sources']=plan['output_sources']
 result=(json.dumps(d,separators=(',',':'))+'\n').encode()
 assert hashlib.sha256(result).hexdigest()==plan['expected_certificate_sha256']
 return result

def main():
 p=argparse.ArgumentParser();p.add_argument('original',type=Path);p.add_argument('output',type=Path);p.add_argument('--plan',type=Path,default=Path(__file__).with_name('plan.json'));a=p.parse_args()
 assert not a.output.exists(),'fresh output required'
 original=a.original.read_bytes();plan_bytes=a.plan.read_bytes();plan=json.loads(plan_bytes)
 data=replay(original,plan);a.output.write_bytes(data)
 print(json.dumps({'status':'PASS_DETERMINISTIC_PLAN_REPLAY','original_sha256':hashlib.sha256(original).hexdigest(),'plan_sha256':hashlib.sha256(plan_bytes).hexdigest(),'replay_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(data).hexdigest(),'nodes':plan['expected_nodes'],'terms':plan['expected_terms'],'expanded_instructions':plan['expected_expanded_instructions'],'solver_invoked':False,'kernel_invoked':False},indent=2))
if __name__=='__main__':main()
