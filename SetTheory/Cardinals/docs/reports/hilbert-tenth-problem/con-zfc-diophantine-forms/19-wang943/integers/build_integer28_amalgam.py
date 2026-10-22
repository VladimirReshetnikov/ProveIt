"""Fresh local normalized-root-merger emitter; upstream JSON is inert data."""
import json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent
path=H/'upstream/09-combined13/arithmetic/amalgam14_product76.json';s=json.loads(path.read_text())
rows=[]
for row in s['source']:
 if row[0]=='strong_diff':row=['normalized_strong_term','*','Delta','I2']
 if row[0]=='Ns':row=['Ns','-','f2','normalized_strong_term']
 rows.append(row)
pos=['J','F','alpha','z','s','eta','zeta'];vs=[v for v in s['witnesses'] if v not in pos+['i','w']]+['i_integer','w_integer'];pre=[]
for x in pos:
 a,b,c=[x+'_positive_'+n for n in 'abc'];vs.extend([a,b,c])
 pre += [[x+'_aa','*',a,a],[x+'_bb','*',b,b],[x+'_cp1','+',c,1],
 [x+'_ccp1','*',c,x+'_cp1'],[x+'_ab','+',x+'_aa',x+'_bb'],[x+'_abc','+',x+'_ab',x+'_ccp1'],[x,'+',x+'_abc',1]]
pre += [['i_double','*',2,'i_integer'],['i','+','i_double',1],['w','*','w_integer','w_integer']]
rows=pre+rows
p={'name':'integer28_normalized_amalgam128_degree258','repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
 'witness_domain':'unrestricted integers','witnesses':vs,'variable_count':28,'fixed_numerals':s['fixed_numerals'],
 'source':rows,'output':'polynomial','exact_degree':258,
 'positive_ports':pos,'coefficient_binding':'Original coherent package06 quartet in upstream/14-integer29/vendor/blank67/k215_constants.json, with beta=Bm1 and K0=Kconstant; MF is shifted.',
 'source_parent':str(path.relative_to(H)),'source_parent_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
 'substitutions':{'positive':'1+a*a+b*b+c*(c+1)','i':'2*i_integer+1','w':'w_integer*w_integer'},
 'ledger':{'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)},
 'factor_degrees':{'N1':35,'Nk':13,'Nt':4,'Ns':66,'guard':140},
 'proof':'INTEGER28_AMALGAM_PROOF.md',
 'leading_monomial_certificate':{'coefficient':'-32*beta^80','exponents':{'J_positive_a':160,'h':1,'gamma':1,'f':4,'i_integer':2,'eta_positive_a':18,'w_integer':26,'s_positive_a':44,'z_positive_a':2},'condition':'beta>0'},
 'formalization_status':'Ordinary mathematical proof, formalizable in ZFC, not newly Lean/Rocq certified.'}
assert len(vs)==28 and len(rows)==128 and p['ledger']['multiplications']==66
(H/'integer28_normalized_amalgam128_degree258.json').write_text(json.dumps(p,indent=2)+'\n')
print(p['name'],p['ledger'])
