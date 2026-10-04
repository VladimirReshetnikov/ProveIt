"""Jointly move paid Q factors to state-block outputs; all predecessors inert."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
PINS={
'matrix193_cleanup_tail_fusion.py':'52113307be60663b792a5ac62a7dc18ca35355d1a534faba4163c9b6d6047089',
'matrix193_cleanup_tail_fusion.json':'61cbef79077bc3c5527c71f0abbeaac967f3d342f83bb8b9019ccdaa89857fe1',
'matrix193_cleanup_tail_fusion.md':'0791bf4f25ae06e5ea4729de70da27d201524b57596756d991ad1af8253ebcc6',
'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
# Removed product -> retained unscaled operand. Every literal multiplication
# and every consumer is checked against the actual parent array.
BLOCKS=[
dict(name='X12',power='r143',exponent=12,aliases={'cp113':'cp112','cp134':'cp133','cp145':'cp144','cp148':'cp147'},outputs=['cp235','cp238']),
dict(name='X48',power='r145',exponent=48,aliases={'cp166':'cp165','cp177':'cp176','cp155':'cp154','cp182':'cp181'},outputs=['cp267','cp270']),
dict(name='Y66',power='cp383',exponent=66,aliases={'cp384':'cp381','cp387':'cp386','cp390':'cp389','cp393':'cp392'},outputs=['cp474','cp477']),
dict(name='Y12',power='r143',exponent=12,aliases={'cp396':'cp395','cp399':'cp398','cp402':'cp401','cp405':'cp404'},outputs=['cp446','cp449']),
dict(name='Y78',power='cp117',exponent=78,aliases={'cp363':'cp362','cp372':'cp371','cp354':'cp353','cp375':'cp374'},outputs=['cp462','cp465'])]
CHANGES={
'cp121':['*','cp383','cp120'],
'cp438':['*','cp434','r161'],'cp439':['*','cp437','r161'],
'cp490':['*','cp486','r138'],'cp491':['*','cp489','r138']}
def need(v,s):
 if not v:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def canon(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def unique(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=unique,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  need(type(r)is list and len(r)==4,'binary row');n,o,a,b=r
  need(type(n)is str and n not in d and o in ['+','-','*'],'SSA/operator')
  need(all(type(v)in [str,int] for v in [a,b]),'operand type');d[n]=r
 return d
def closure(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in d:todo.extend(d[n][2:])
 return seen
def count(rows):
 c=Counter(r[1] for r in rows);return dict(total=len(rows),M=c['*'],A=c['+']+c['-'])
def audit(rows,free,fixed,output):
 d=table(rows);seen=set(free);need(len(seen)==len(free),'unique free ports');degree={n:int(n not in fixed) for n in seen}
 for n,o,a,b in rows:
  need(n not in seen and all(type(v)is int or v in seen for v in [a,b]),'sequential source')
  x,y=[0 if type(v)is int else degree[v] for v in [a,b]];degree[n]=x+y if o=='*' else max(x,y);seen.add(n)
 need(closure(d,[output])==seen,'complete live source and free interface')
 return dict(count(rows),syntactic_degree_upper=degree[output],all_live=True)
def add(a,b,s=1):
 d=dict(a)
 for k,c in b.items():d[k]=d.get(k,0)+s*c
 return {k:c for k,c in d.items() if c}
def mul(a,b):
 d={}
 for k,c in a.items():
  for j,v in b.items():d[k+j]=d.get(k+j,0)+c*v
 return {k:c for k,c in d.items() if c}
def plist(p):return [[k,v] for k,v in sorted(p.items())]
def expand_pair(old,new,Q,free):
 # Exact polynomial normalization for every pure-Q cone, anchored to the
 # same actual computed Q; all other expressions remain exact DAG nodes.
 pool={}
 def atom(x):
  if x not in pool:pool[x]=len(pool)
  return pool[x]
 seeds={n:atom(('port',n)) for n in free};allv=[];allp=[]
 for rows in [old,new]:
  v=dict(seeds);p={};qnode=None
  for n,o,a,b in rows:
   def val(x):return atom(('integer',x)) if type(x)is int else v[x]
   if n==Q:
    v[n]=atom((o,val(a),val(b)));qnode=v[n];p[n]={1:1}
   elif all(type(x)is int or x in p for x in [a,b]):
    x={0:a} if type(a)is int else p[a];y={0:b} if type(b)is int else p[b]
    p[n]=mul(x,y) if o=='*' else add(x,y,1 if o=='+' else -1)
    v[n]=atom(('polynomial_in_actual_Q',qnode,tuple(sorted(p[n].items()))))
   else:v[n]=atom((o,val(a),val(b)))
  allv.append(v);allp.append(p)
 need(allv[0][Q]==allv[1][Q],'identical actual computed Q')
 return allv,allp
def rewrite(parent,m):
 old=parent['source'];d={n:r[:] for n,r in table(old).items()};deleted={};introduced=[];restored=[]
 for block in BLOCKS:
  power=m(block['power'])
  for target,operand in block['aliases'].items():
   t,a=m(target),m(operand);r=d[t]
   need(r[1]=='*' and sorted(r[2:])==sorted([a,power]),'literal removable factor '+t)
   deleted[t]=a
  for n in block['outputs']:
   n=m(n);r=d[n];need(r[1]=='+','terminal contribution sum')
   inner='joint_factor_'+n
   need(inner not in d and inner not in parent['free'],'fresh factor name')
   d[inner]=[inner,r[1],r[2],r[3]];d[n]=[n,'*',inner,power]
   introduced.append(inner);restored.append(n)
 for n,r in CHANGES.items():
  n=m(n);need(n in d,'changed factor register');d[n]=[n,r[0],m(r[1]),m(r[2])]
 for n in deleted:del d[n]
 for n,r in list(d.items()):d[n]=[n,r[1],deleted.get(r[2],r[2]),deleted.get(r[3],r[3])]
 out=[];done=set();active=set()
 def emit(n):
  if type(n)is int or n not in d or n in done:return
  need(n not in active,'cycle after simultaneous rewrites');active.add(n)
  for x in d[n][2:]:emit(x)
  active.remove(n);done.add(n);out.append(d[n])
 for r in old:
  if r[0] in d:emit(r[0])
 emit(parent['output']);need(done==set(d),'all new rows scheduled')
 return out,dict(deleted_aliases=deleted,introduced= introduced,restored_targets=restored)
def finalizer(rows,output,unit):
 d=table(rows);out=set();r=d[output];need(r[1]=='-' and r[3]==1,'final offset');out.add(r[0])
 r=d[r[2]];need(r[1]=='*' and r[2]==unit,'native multiplier');out.add(r[0]);r=d[r[3]]
 need(r[1]=='+' and r[3]==1,'positive SOS offset');out.add(r[0]);res=[]
 def walk(n):
  r=d[n];out.add(n)
  if r[1]=='*':need(r[2]==r[3],'square');res.append(r[2]);out.add(r[2]);return
  need(r[1]=='+','SOS addition');walk(r[2]);walk(r[3])
 walk(r[2]);return {n:d[n] for n in out},res
def build(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'inert dependency '+n)
 parent=read(root/'matrix193_cleanup_tail_fusion.json');maps=read(root/'matrix193_entry_controller_charts.json')
 before=canon(parent);need(parent['source_sha256']==PINS['matrix193_cleanup_tail_fusion.py'],'parent helper binding')
 oldpackets=parent['packets'];need(len(oldpackets)==4,'four parent arrays');packets=[]
 baseline=oldpackets[0];base_names=[r[0] for r in baseline['source']]
 # These rows are interleaved with packing producers after topological
 # rescheduling; never infer the native boundary from a contiguous slice.
 native=[n for n in base_names if n.startswith('selection__') and n not in ['selection__wn2','selection__R10b']]+[
  'unit_pair','first_gap_square','first_root_base','first_signed_gap','first_cross','first_four_cross','first_unit','four_units',
  'packed_middle_sum','packed_middle_product','packed_top_sum','index_unit','five_units','linear_difference','twice_index_difference',
  'linear_unit','six_units','strong_unit_difference','strong_unit','seven_units',
  'r818','r819','r820','r821','r822','r823','joint_bound_unit','eight_units']
 grouped=['r'+str(i) for i in range(110,134)]+[n for n in base_names if n.startswith('grouped_population_sum_')]+['r103']
 need(len(native)==63 and len(grouped)==97,'native/group boundaries')
 for j,p in enumerate(oldpackets):
  mapping={} if j==0 else maps['packets'][j-1]['map'];m=lambda n:mapping.get(n,n) if type(n)is str else n
  old=p['source'];od=table(old);need(p['source_sha256']==sha(canon(old)),'complete parent binding')
  for row in baseline['coefficient_component']:
   r=[m(row[0]),row[1],m(row[2]),m(row[3])];need(od[r[0]]==r,'complete550 chart mapping')
  new,plan=rewrite(p,m);nd=table(new)
  need(len(plan['deleted_aliases'])==20 and len(plan['introduced'])==10,'exact20 removed/10 new')
  need(set(od)-set(nd)==set(plan['deleted_aliases']) and set(nd)-set(od)==set(plan['introduced']),'complete changed-name sets')
  a0=audit(old,p['free'],p['fixed_numerals'],p['output']);a1=audit(new,p['free'],p['fixed_numerals'],p['output'])
  need(a1['total']==a0['total']-10 and a1['M']==a0['M']-10 and a1['A']==a0['A'],'ten paid multiplication saving')
  values,polys=expand_pair(old,new,m('r108'),p['free']);pv,pn=values;po,pp=polys
  for n,e in [('r143',12),('r145',48),('cp383',66),('cp117',78),('r161',72),('r138',18)]:
   need(po[m(n)]==pp[m(n)]=={e:1},'actual retained factor power')
  different=[];same=0
  for n in set(od)&set(nd):
   if pv[n]==pn[n]:same+=1;continue
   need(n in {r[0] for r in p['coefficient_component']},'only coefficient intermediates may change value')
   need(n in po and n in pp and po[n] and pp[n],'only pure-Q intermediates may change')
   shift=min(po[n])-min(pp[n]);need(shift in [12,48,66,78],'declared extracted factor')
   need(po[n]=={k+shift:v for k,v in pp[n].items()},'exact shifted intermediate identity')
   different.append(dict(register=n,extracted_Q_power=shift,old_polynomial_sha256=sha(canon(plist(po[n]))),new_polynomial_sha256=sha(canon(plist(pp[n])))))
  need(pv[p['output']]==pn[p['output']],'entire polynomial identity')
  restored_names=plan['restored_targets']+[m(n) for n in ['cp438','cp439','cp490','cp491']]
  need(all(pv[n]==pn[n] for n in restored_names),'all14 restored contributions')
  restored=[dict(register=n,actual_Q=m('r108'),ascending_nonzero_coefficients=plist(po[n]),
   old_definition=od[n],new_definition=nd[n]) for n in restored_names]
  words=[]
  for cert in p['coefficient_certificates']:
   n=cert['wire'];expected={k:v for k,v in enumerate(cert['ascending_coefficients']) if v}
   need(po[n]==pp[n]==expected,'full coefficient word exact')
   words.append(dict(wire=n,coefficients=len(cert['ascending_coefficients']),sha256=sha(canon(plist(expected)))))
  component_ids={r[0] for r in p['coefficient_component']}|set(plan['introduced'])
  component=[r for r in new if r[0] in component_ids];need(count(component)==dict(total=540,M=292,A=248),'full540 coefficient cone')
  selector=p['shared_selector_component'];need(len(selector)==242 and all(nd[r[0]]==r for r in selector),'selector242 literal')
  need(all(nd[m(n)]==od[m(n)] for n in native+grouped),'native63/group97 literal')
  fo,ro=finalizer(old,p['output'],m('eight_units'));fn,rn=finalizer(new,p['output'],m('eight_units'))
  need(fo==fn and ro==rn==p['retained_residual_wires'],'literal complete finalizer/residuals')
  need(all(nd[n]==r for n,r in od.items() if n not in component_ids),'all external rows literal')
  ledger=dict(a1,positive_witnesses=len(p['witnesses']),supplied_ports=len(p['free']),fixed_coefficient_ports=len(p['fixed_numerals']),
   exact_degree=p['ledger']['exact_degree'],outer_residuals=len(rn),integer_literals=len({v for r in new for v in r[2:] if type(v)is int}))
  need((ledger['total'],ledger['positive_witnesses'],ledger['exact_degree'])==[(1405,141,35587),(1402,140,53345),(1402,140,53347),(1399,139,71105)][j],'complete ledger')
  packet={k:p[k] for k in ['variant','free','fixed_numerals','witnesses','fixture_fixed_bindings','output','retained_residual_wires','coefficient_certificates','selector_words','selector_ledger']}
  packet.update(source=new,source_sha256=sha(canon(new)),ledger=ledger,coefficient_component=component,component_ledger=count(component),
   shared_selector_component=[r for r in new if r[0] in {x[0] for x in selector}],
   parent_reference=dict(receipt='matrix193_cleanup_tail_fusion.json',packet_index=j,source_sha256=sha(canon(old))),
   proof=dict(actual_Q=m('r108'),plan=plan,changed_internal_values=sorted(different,key=lambda x:x['register']),retained_values_identical=same,
    restored_contributions=restored,coefficient_words=words,whole_polynomial_identity=True),
   boundaries=dict(selector_literal=242,native_literal=63,group_population_literal=97,finalizer_literal=len(fn),ordinary_residuals_literal=len(rn)))
  packets.append(packet)
 need(canon(parent)==before,'parent object unchanged')
 return dict(status='PASS_MATRIX_JOINT_STATE_FACTOR',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,blocks=BLOCKS,other_definitions=CHANGES,packets=packets,
  scope=dict(all_ring_complete_identity=True,changed_internal_values_are_not_witnesses=True,positive_zero_map='identity to immediate parent',
   older_terminal_IDLE_inverse='ordinary-input only',exact_degrees_inherited=True,new_native_fixture=False,predecessor_execution=False))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:need(canon(r)==canon(read(a.expect)),'exact type-sensitive receipt')
 print(r['status'],[p['ledger']['total'] for p in r['packets']],'component540; all four full polynomial identities')
if __name__=='__main__':main()
