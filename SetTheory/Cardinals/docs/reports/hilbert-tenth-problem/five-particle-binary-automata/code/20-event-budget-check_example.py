"""Binding verifier for the sample artifact, using its normative small compiler.
This is not an independent arbitrary-mass compiler. All values are exact ints.
"""
import json
from pathlib import Path
import example_emitter as e
H=Path(__file__).resolve().parent

def strict_equal(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(strict_equal(a[k],b[k]) for k in a)
    if type(a) in (tuple,list):return len(a)==len(b) and all(strict_equal(x,y) for x,y in zip(a,b))
    return a==b

def validate_polynomial(rows,arity,degree):
    if type(rows) is not list:raise ValueError('polynomial row list required')
    for row in rows:
        if type(row) is not list:raise ValueError('row must be a list')
        seen=set()
        for term in row:
            if type(term) is not list or len(term)!=2:raise ValueError('coefficient/monomial pair required')
            coefficient,monomial=term
            if type(coefficient) is not int or coefficient==0:raise ValueError('nonzero exact-integer coefficient required')
            if type(monomial) is not list or len(monomial)>degree or any(type(i) is not int or i<0 or i>=arity for i in monomial):raise ValueError('invalid monomial')
            key=tuple(monomial)
            if monomial!=sorted(monomial) or key in seen:raise ValueError('noncanonical monomial list')
            seen.add(key)

def check_artifact(data,witness):
    if not isinstance(witness,list) or any(type(v) is not int or v<0 for v in witness):raise ValueError('natural witness required')
    inputs=data['input_values']
    if len(inputs)!=3 or any(type(v) is not int or v<0 for v in inputs):raise ValueError('natural input required')
    expected_source=dict(schema='reversible-two-counter-v1',controls=['q','halt'],start='q',halt='halt',class_cut=0,
             branches=[dict(name='e',source='q',target='halt',side=1,delta=1,guard=dict(op='true'))])
    if not strict_equal(data['source'],expected_source):raise ValueError('source binding')
    c,rounds,output=e.build(inputs[0]-inputs[1],inputs[2]+1,data['T'],data['K'],data['target'])
    if c.values[:3]!=inputs:raise ValueError('noncanonical signed input')
    if type(data['input_count']) is not int or data['input_count']!=3 or len(witness)!=len(c.values)-3:raise ValueError('arity binding')
    if data['variable_names']!=c.names:raise ValueError('variable ordering binding')
    if not strict_equal(data['ledger'],c.ledger()):raise ValueError('ledger binding')
    validate_polynomial(data['residuals'],len(c.values),2)
    validate_polynomial([data['expanded_quartic']],len(c.values),4)
    if not strict_equal(data['residuals'],[e.dump_poly(p) for p in c.rows]):raise ValueError('residual binding')
    if not strict_equal(data['expanded_quartic'],e.dump_poly(c.expanded())):raise ValueError('expansion binding')
    if not strict_equal(data['rounds'],rounds) or not strict_equal(data['output'],output):raise ValueError('decoder binding')
    values=inputs+witness
    if c.score(values):raise ValueError('nonzero polynomial')
    return dict(status='passed',witnesses=len(witness),residuals=len(c.rows),output=output)

if __name__=='__main__':
    data=json.loads((H/'example-polynomial.json').read_text());w=json.loads((H/'example-witness.json').read_text())
    result=check_artifact(data,w)
    rejected=0
    for field,value in [('K',1),('T',2),('target',[0,1]),('residuals',data['residuals'][:-1])]:
        bad=dict(data);bad[field]=value
        try:check_artifact(bad,w)
        except ValueError:rejected+=1
        else:raise RuntimeError(('mutation accepted',field))
    result['declaration_mutations_rejected']=rejected
    (H/'binding-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
