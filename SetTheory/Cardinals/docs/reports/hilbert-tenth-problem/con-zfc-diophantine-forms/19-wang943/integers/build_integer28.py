"""Fresh local emitter. Treats the pinned parent circuit as inert JSON only."""
import hashlib,json
from pathlib import Path
H=Path(__file__).resolve().parent
p=H/'upstream/12-gap-norm14/arithmetic/blank14_gap_norm75.json'
src=json.loads(p.read_text())
positive=['Jrep','F','alpha','transport_quotient','s','eta','zeta']
pre=[]
variables=[x for x in src['witnesses'] if x not in positive+['i','w']]+['i_integer','w_integer']
for x in positive:
 a,b,c=[x+'_positive_'+z for z in 'abc'];variables += [a,b,c]
 pre += [[x+'_aa','*',a,a],[x+'_bb','*',b,b],[x+'_cp1','+',c,1],
         [x+'_ccp1','*',c,x+'_cp1'],[x+'_ab','+',x+'_aa',x+'_bb'],
         [x+'_abc','+',x+'_ab',x+'_ccp1'],[x,'+',x+'_abc',1]]
pre += [['i_double','*',2,'i_integer'],['i','+','i_double',1],['w','*','w_integer','w_integer']]
rows=pre+src['source'];M=sum(x[1]=='*' for x in rows)
assert len(variables)==28 and len(rows)==127 and M==66
result={'name':'integer28_gap_norm127_degree426','repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
 'description':'Seven positivity surjections, odd strong multiplier, square power scale, and gap-root elimination.',
 'witness_domain':'unrestricted integers','witnesses':variables,'variable_count':28,
 'fixed_numerals':src['fixed_numerals'],
 'coefficient_binding':'Original coherent package06 quartet, as specified in upstream/14-integer29/vendor/blank67/k215_constants.json; MF is shifted. The four fixed numerals are not unknowns.',
 'source_parent':str(p.relative_to(H)),'source_parent_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'proof':'INTEGER28_PROOF.md','positive_ports':positive,
 'substitutions':{'positive':'x=a*a+b*b+c*(c+1)+1','i':'2*i_integer+1','w':'w_integer*w_integer'},
 'source':rows,'output':src['output'],'exact_degree':426,
 'factor_degrees':{'norm_first':44,'norm_main':35,'norm_index':13,'norm_transport':4,'gg_unit':330},
 'ledger':{'operations':127,'multiplications':66,'additions_subtractions':61},
 'leading_monomial_certificate':{'coefficient':'-8192*Bm1^134',
   'exponents':{'Jrep_positive_a':268,'h':1,'gamma':1,'auxiliary_gap':2,'i_integer':8,
     'eta_positive_a':38,'w_integer':34,'s_positive_a':72,'transport_quotient_positive_a':2},
   'condition':'Bm1>0','degree':426},
 'formalization_status':'Ordinary mathematical proof, formalizable in ZFC, not newly Lean/Rocq certified.'}
out=H/'integer28_gap_norm127_degree426.json';out.write_text(json.dumps(result,indent=2)+'\n')
print(out.name)
