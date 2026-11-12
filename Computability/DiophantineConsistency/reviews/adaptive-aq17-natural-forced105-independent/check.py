#!/usr/bin/env python3
"""Full mixed-shift polynomial comparison and forcing-wiring audit."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-aq17-factored-root94/candidate.json','7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a'))
c=json.loads(pin('research/adaptive-aq17-natural-forced105/candidate.json','ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac'))
pin('research/adaptive-aq17-natural-forced105/receipt.json','322913d757b9cac60fb64b7c446026e0922c2d6f782456b8fe5de1f74fecec84')
pin('reviews/adaptive-aq17-factored-root94-independent/result.json','0b206d5f4e0652c6d9c7bd63855585cc7a0453802b1dfdf921dd68edb5e289ea')
mid=json.loads(pin('research/adaptive-aq17-natural-forced108/candidate.json','de138a3caa5528765aa380abe9827bdd36c569a865d9a02cb21fbf07b241e28f'))
pin('research/adaptive-aq17-natural-forced108/receipt.json','d038739ae82ac08c4c5728194b7b8849df6ce613e46177d05bf4bbff592f6e7c')
midforced={'firstQuotient','mainQuotient','vValueVariable'}
assert mid['forced_unshifted']==sorted(midforced) and len(mid['source'])==108
midren={x:'n_'+x for x in p['witnesses']};midrep=lambda x:('shift_'+x if x in midren and x not in midforced else midren.get(x,x)) if isinstance(x,str) else x
assert mid['witnesses']==list(midren.values()) and mid['source']==[['shift_'+x,'+',midren[x],1] for x in p['witnesses'] if x not in midforced]+[[x,op,midrep(a),midrep(b)] for x,op,a,b in p['source']]
forced={'f','T','y','firstQuotient','mainQuotient','vValueVariable'}
assert c['forced_unshifted']==sorted(forced) and len(p['witnesses'])==len(c['witnesses'])==17
assert len(p['source'])==94 and len(c['source'])==105
ren={x:'n_'+x for x in p['witnesses']};rep=lambda x:('shift_'+x if x in ren and x not in forced else ren.get(x,x)) if isinstance(x,str) else x
assert c['witnesses']==list(ren.values()) and c['source']==[['shift_'+x,'+',ren[x],1] for x in p['witnesses'] if x not in forced]+[[x,op,rep(a),rep(b)] for x,op,a,b in p['source']]
assert c['output']==p['output'] and c['fixed_numerals']==p['fixed_numerals']
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
def run(g,subs):
 env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']};env.update(subs);rows={}
 for name,op,a,b in g['source']:
  assert name not in env and op in '+-*';rows[name]=(a,b)
  a=env[a] if isinstance(a,str) else ({():a} if a else {})
  b=env[b] if isinstance(b,str) else ({():b} if b else {})
  env[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 active={g['output']};todo=[g['output']]
 while todo:
  for x in rows.get(todo.pop(),()):
   if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
 assert set(rows)|set(g['witnesses'])|set(g['fixed_numerals'])<=active
 return env
subs={x:(atom(ren[x]) if x in forced else add(atom(ren[x]),{():1})) for x in p['witnesses']}
a,b=run(p,subs),run(c,{})
res=['A0','A1','auxResidual','g72','rankDifference','zDifference','dDifference','vDifference']
assert a[p['output']]==b[c['output']] and all(a[x]==b[x] for x in res)
# Bind the six zero-forcing arguments to the exact parent graph wiring.
rows={row[0]:row for row in p['source']}
for row in [['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['c','+','eta','kY'],['c2','*','c','c'],['ell','*','E','kY'],['a','+','E','Y'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['DeltaComputed','+','H','g17'],['g38','*','firstQuotient','firstQuotient'],['g30','+','ell','k'],['g40','*','ell','g30'],['g41','+',1,'g40'],['A0','-','g38','g41'],['g61','*','mainQuotient','mainQuotient'],['g63','*','DeltaComputed','c2'],['g64','+',1,'g63'],['A1','-','g61','g64'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','QComputed'],['y2','*','y','y'],['g80','*','vValueVariable','vValueVariable'],['g81','-','y2','g80'],['g82','*','QComputed','g81'],['Fa','-','y2','g82'],['auxResidual','-','Fa',1],['f2','*','f','f'],['rho','-','f2',1],['QComputed','*','DeltaComputed','rho'],['g74','*','T','c'],['g75','-','g74','rankVariable'],['g76','*','f2','g75'],['VComputed','-','g76','c'],['vDifference','-','vValueVariable','VComputed']]:assert rows[row[0]]==row,row
# Sum-of-eight-squares identity in formal residual symbols.
env={x:atom(x) for x in res}
for name,op,x,y in c['source']:
 if name in env or (isinstance(x,str) and x not in env) or (isinstance(y,str) and y not in env):continue
 x=env[x] if isinstance(x,str) else ({():x} if x else {});y=env[y] if isinstance(y,str) else ({():y} if y else {})
 env[name]=mul(x,y) if op=='*' else add(x,y,-1 if op=='-' else 1)
assert env[c['output']]=={(x,x):1 for x in res}
inputs=set(c['witnesses']);out=b[c['output']];degree=lambda mon:sum(x in inputs for x in mon)
assert max(map(degree,out))==20
witness=tuple(sorted(['n_Y']*8+['n_eta']*8+['n_i']*4));coeff={tuple(x for x in mon if x not in inputs):v for mon,v in out.items() if tuple(x for x in mon if x in inputs)==witness}
assert coeff=={():1}
print(json.dumps({'scope':'full mixed-substitution polynomial, graph wiring, external model argument; no Lean','variables':17,'natural_operations':105,'forced_unshifted':sorted(forced),'output_terms':len(out),'degree_every_integer_port_tuple':20,'degree20_witness_coefficient':1,'all_rows_inputs_ports_live':True,'sum_of_squares':8,'intermediate_108_shift_rows_verified':True,'no_literal_iPRA_or_lean_proof':True},sort_keys=True,indent=2))
