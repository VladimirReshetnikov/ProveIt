"""Fresh local emitter for the signed four-root construction."""
import json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent
src=H.parent/'roots/root12_saturated_product.json';data=src.read_bytes()
assert hashlib.sha256(data).hexdigest()=='fbfa374237b93dc02da02bf2b13387e7751fc826dd28758385e77c698841554c'
p=json.loads(data);rows=[];replaced=0
v2matches=[n for n,op,a,b in p['source'] if op=='*' and a==b=='vaux']
assert len(v2matches)==1
v2register=v2matches[0]
for n,op,a,b in p['source']:
 if op=='*' and {a,b}=={'Saux','vaux'}:
  rows += [['S_absolute_bound','*','Saux','i'],[n,'*','S_absolute_bound',v2register]];replaced+=1
 else:rows.append([n,op,a,b])
assert replaced==1
pos=['J','F','alpha','z','s','eta','zeta'];vs=[x for x in p['witnesses'] if x not in pos+['i','w']]+['i_integer','w_integer'];pre=[]
for x in pos:
 a,b,c=[x+'_positive_'+n for n in 'abc'];vs.extend([a,b,c])
 pre += [[x+'_aa','*',a,a],[x+'_bb','*',b,b],[x+'_cp1','+',c,1],
 [x+'_ccp1','*',c,x+'_cp1'],[x+'_ab','+',x+'_aa',x+'_bb'],[x+'_abc','+',x+'_ab',x+'_ccp1'],[x,'+',x+'_abc',1]]
pre += [['i_double','*',2,'i_integer'],['i','+','i_double',1],['w','*','w_integer','w_integer']]
rows=pre+rows
out={'name':'integer26_unscaled_four_root192_degree2465','repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
 'witness_domain':'unrestricted integers','witnesses':vs,'variable_count':26,'fixed_numerals':['beta','K0','MC','MF'],
 'source':rows,'output':p['output'],'exact_degree':2465,'resultant_exact_degree':2448,
 'positive_ports':pos,'coefficient_binding':'COEFFICIENT_BINDINGS.json selects the complete compact Wang943 quartet (d=5^10) for the primary instantiation, with coherent original06 and Wang9435^11 alternatives; MF is shifted.',
 'source_parent':'../roots/root12_saturated_product.json','source_parent_sha256':hashlib.sha256(data).hexdigest(),
 'sign_safe_bound':'W=2*((S*i)*(v*v)+b), S=Delta*i*c^2, v=c*T',
 'substitutions':{'positive':'1+a*a+b*b+c*(c+1)','i':'2*i_integer+1','w':'w_integer*w_integer'},
 'ledger':{'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)},
 'proof':'INTEGER26_UNSCALED_PROOF.md','factor_degrees':{'Nk':13,'Nt':4,'unit12':2448},
 'leading_monomial_certificate':{'coefficient':'2^124*3^8*beta^789','exponents':{'J_positive_a':1578,'h':1,'i_integer':48,'eta_positive_a':224,'w_integer':194,'s_positive_a':418,'z_positive_a':2},'condition':'beta>0'},
 'formalization_status':'Ordinary mathematical proof, formalizable in ZFC, not newly Lean/Rocq certified.'}
assert len(vs)==26 and len(rows)==192 and out['ledger']['multiplications']==117
(H/'integer26_unscaled_four_root192_degree2465.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['name'],out['ledger'])
