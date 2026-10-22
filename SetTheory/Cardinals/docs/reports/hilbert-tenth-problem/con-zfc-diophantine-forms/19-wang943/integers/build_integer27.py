"""Fresh local27-integer weighted-root emitter."""
import json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent;path=H/'upstream/09-combined13/arithmetic/polynomial13_84.json';p=json.loads(path.read_text())
pos=['Jrep','F','alpha','transport_quotient','s','eta','zeta'];vs=[x for x in p['witnesses'] if x not in pos+['i','w']]+['i_integer','w_integer'];pre=[]
for x in pos:
 a,b,c=[x+'_positive_'+n for n in 'abc'];vs.extend([a,b,c]);pre += [[x+'_aa','*',a,a],[x+'_bb','*',b,b],[x+'_cp1','+',c,1],[x+'_ccp1','*',c,x+'_cp1'],[x+'_ab','+',x+'_aa',x+'_bb'],[x+'_abc','+',x+'_ab',x+'_ccp1'],[x,'+',x+'_abc',1]]
pre += [['i_double','*',2,'i_integer'],['i','+','i_double',1],['w','*','w_integer','w_integer']];rows=pre+p['source']
out={'name':'integer27_weighted_root136_degree1116','repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035','witness_domain':'unrestricted integers','witnesses':vs,'variable_count':27,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'exact_degree':1116,'positive_ports':pos,
'coefficient_binding':'Original coherent package06 quartet in upstream/14-integer29/vendor/blank67/k215_constants.json; MF is shifted.',
'source_parent':str(path.relative_to(H)),'source_parent_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
'substitutions':{'positive':'1+a*a+b*b+c*(c+1)','i':'2*i_integer+1','w':'w_integer*w_integer'},
'ledger':{'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)},
'factor_degrees':{'norm_main':35,'norm_index':13,'norm_transport':4,'unit13':1064},'proof':'INTEGER27_PROOF.md',
'leading_monomial_certificate':{'coefficient':'2^27*Bm1^344','exponents':{'Jrep_positive_a':688,'h':1,'gamma':1,'i_integer':24,'eta_positive_a':114,'w_integer':86,'s_positive_a':200,'transport_quotient_positive_a':2},'condition':'Bm1>0'}}
assert len(vs)==27 and len(rows)==136 and out['ledger']['multiplications']==72
(H/'integer27_weighted_root136_degree1116.json').write_text(json.dumps(out,indent=2)+'\n');print(out['name'],out['ledger'])
