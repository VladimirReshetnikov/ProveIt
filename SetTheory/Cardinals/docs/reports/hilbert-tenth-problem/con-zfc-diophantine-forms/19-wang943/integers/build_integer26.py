"""Fresh local emitter for the signed four-root construction."""
import json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent
src=H.parent/'roots/root12_scaled_y_product.json';data=src.read_bytes()
assert hashlib.sha256(data).hexdigest()=='8b2f4c0152de2d6e8af6ddd1aaee6eec0122492eee32a484cdd88de5694c68b9'
p=json.loads(data);rows=[];replaced=0
for n,op,a,b in p['source']:
 if op=='*' and {a,b}=={'Saux','vaux'}:
  rows += [['S_absolute_bound','*','Saux','i'],['v_absolute_bound','*','vaux','T'],[n,'*','S_absolute_bound','v_absolute_bound']];replaced+=1
 else:rows.append([n,op,a,b])
assert replaced==1
pos=['J','F','alpha','z','s','eta','zeta'];vs=[x for x in p['witnesses'] if x not in pos+['i','w']]+['i_integer','w_integer'];pre=[]
for x in pos:
 a,b,c=[x+'_positive_'+n for n in 'abc'];vs.extend([a,b,c])
 pre += [[x+'_aa','*',a,a],[x+'_bb','*',b,b],[x+'_cp1','+',c,1],
 [x+'_ccp1','*',c,x+'_cp1'],[x+'_ab','+',x+'_aa',x+'_bb'],[x+'_abc','+',x+'_ab',x+'_ccp1'],[x,'+',x+'_abc',1]]
pre += [['i_double','*',2,'i_integer'],['i','+','i_double',1],['w','*','w_integer','w_integer']]
rows=pre+rows
out={'name':'integer26_four_root194_degree3185','repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
 'witness_domain':'unrestricted integers','witnesses':vs,'variable_count':26,'fixed_numerals':['beta','K0','MC','MF'],
 'source':rows,'output':p['output'],'exact_degree':3185,'resultant_exact_degree':3168,
 'positive_ports':pos,'coefficient_binding':'COEFFICIENT_BINDINGS.json selects the complete compact Wang943 quartet (d=5^10) for the primary instantiation, with coherent original06 and Wang9435^11 alternatives; MF is shifted.',
 'source_parent':'../roots/root12_scaled_y_product.json','source_parent_sha256':hashlib.sha256(data).hexdigest(),
 'sign_safe_bound':'W=2*(Q-1)*((S*i)*(v*T)+b), S=Delta*i*c^2, v=c*T',
 'substitutions':{'positive':'1+a*a+b*b+c*(c+1)','i':'2*i_integer+1','w':'w_integer*w_integer'},
 'ledger':{'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)},
 'proof':'INTEGER26_PROOF.md','factor_degrees':{'Nk':13,'Nt':4,'unit12':3168},
 'leading_monomial_certificate':{'coefficient':'2^140*3^8*beta^1013','exponents':{'J_positive_a':2026,'h':1,'i_integer':64,'eta_positive_a':288,'w_integer':258,'s_positive_a':546,'z_positive_a':2},'condition':'beta>0'},
 'formalization_status':'Ordinary mathematical proof, formalizable in ZFC, not newly Lean/Rocq certified.'}
assert len(vs)==26 and len(rows)==194 and out['ledger']['multiplications']==119
(H/'integer26_four_root194_degree3185.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['name'],out['ledger'])
