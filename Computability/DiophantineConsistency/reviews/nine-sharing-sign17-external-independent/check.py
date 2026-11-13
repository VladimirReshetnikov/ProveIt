#!/usr/bin/env python3
"""Independent sign17 substitution, positive-lift structure and degree witness audit."""
import gzip,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';oldp=research/'nine-sharing-sign18-degree94-root-candidate/seed.json';newp=research/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(oldp.read_bytes())=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb' and sha(newp.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';old=json.loads(oldp.read_text());new=json.loads(newp.read_text());assert old['witness_count']==18 and new['witness_count']==17 and new['total_coordinates']==18 and old['distinguished_input_coordinate']==new['distinguished_input_coordinate']==0 and old['fixed_ports']==new['fixed_ports'] and old['coefficient_binding']==new['coefficient_binding']
f=['add',['var',13],['num',1]];v=['var',17];delta=['sub',['mul',f,f],['mul',v,v]];removed=[x for x in old['residuals'] if x['gate']=='V2minusY2'];assert len(removed)==1 and removed[0]['kind']=='signed' and removed[0]['expr']==['sub',['var',18],delta] and new['lift_expression']==delta
def replace(t):
 if t[0]=='var':return delta if t[1]==18 else t
 if t[0] in ('port','num'):return t
 assert t[0] in ('add','sub','mul');return [t[0],replace(t[1]),replace(t[2])]
a=[r for r in old['residuals'] if r['gate']!='V2minusY2'];b=new['residuals'];assert len(a)==len(b)==8
for x,y in zip(a,b):assert {k:v for k,v in x.items() if k!='expr'}=={k:v for k,v in y.items() if k!='expr'} and replace(x['expr'])==y['expr']
na=next(x['expr'] for x in a if x['gate']=='Na');assert na[0]=='sub' and na[2]==['num',1] and na[1][0]=='sub' and na[1][1]==['mul',f,f] and na[1][2][0]=='mul' and na[1][2][2]==['var',18];square=na[1][2][1];assert square[0]=='mul' and square[1]==square[2];factor=square[1];assert factor[0]=='mul' and factor[1]==['add',['var',6],['num',1]] and factor[2][0]=='mul';R=factor[2][1];assert factor[2][2]==['add',R,['num',2]] and R==old['lift_expression']
beta_term=['mul',['port','beta'],['add',['var',1],['num',1]]]
def positive_syntax(t):
 if t[0]=='num':return type(t[1]) is int and t[1]>=0
 if t[0] in ('var','port'):return True
 return t[0] in ('add','mul') and positive_syntax(t[1]) and positive_syntax(t[2])
def additive_terms(t):return additive_terms(t[1])+additive_terms(t[2]) if t[0]=='add' else [t]
assert positive_syntax(R) and beta_term in additive_terms(R)
def deg(t):
 if t[0]=='var':assert 0<=t[1]<18;return 1
 if t[0] in ('num','port'):return 0
 x,y=deg(t[1]),deg(t[2]);return x+y if t[0]=='mul' else max(x,y)
degrees={r['gate']:deg(r['expr']) for r in b};assert max(degrees.values())==48
# Sparse polynomial evaluation of Na on v1..v16=t, v17=0; input v0 is forbidden.
def poly(t):
 if t[0]=='num':return {(0,0):t[1]} if t[1] else {}
 if t[0]=='port':assert t[1]=='beta';return {(0,1):1}
 if t[0]=='var':assert t[1]!=0;return {(1,0):1} if 1<=t[1]<=16 else {}
 x,y=poly(t[1]),poly(t[2]);z={}
 if t[0] in ('add','sub'):
  for key,val in x.items():z[key]=z.get(key,0)+val
  for key,val in y.items():z[key]=z.get(key,0)+(val if t[0]=='add' else -val)
 else:
  assert t[0]=='mul'
  for (i,j),u in x.items():
   for (k,l),v0 in y.items():z[(i+k,j+l)]=z.get((i+k,j+l),0)+u*v0
 return {key:val for key,val in z.items() if val}
q=poly(next(r['expr'] for r in b if r['gate']=='Na'));assert {k:v for k,v in q.items() if k[0]>=48}=={(48,28):-16}
records={};binding=new['coefficient_binding']
for name,rec in binding['ports'].items():
 packed=(newp.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==rec['raw_bytes'];records[name]=len(raw)
 if name=='beta':assert int.from_bytes(raw,'big')>0
assert set(records)=={'beta','K0','MC','MF'}
print(json.dumps({'status':'PASS_EXTERNAL_INDEPENDENT','source_sha256':sha(oldp.read_bytes()),'candidate_sha256':sha(newp.read_bytes()),'residual_degrees':degrees,'Na_t48':'-16*beta^28','fixed_positive_beta_degree':96,'lift_condition':'beta > 0 and retained Na=0','scope':'external arithmetic/AST audit; no Lean/model/iPRA bridge'},indent=2,sort_keys=True))
