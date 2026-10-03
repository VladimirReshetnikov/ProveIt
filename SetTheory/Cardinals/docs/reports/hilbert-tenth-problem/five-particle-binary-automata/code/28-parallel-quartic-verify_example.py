"""Validate and verify the concrete polynomial without importing its emitter."""
from pathlib import Path
import json,hashlib

class ValidationError(ValueError):
    pass

def check(condition,detail):
    if not condition:raise ValidationError(detail)

def object_schema(value,keys,label):
    check(type(value)is dict and set(value)==set(keys),label+' schema')

def integer(value,label,minimum=None):
    check(type(value)is int,label+' must be an exact integer')
    if minimum is not None:check(value>=minimum,label+' is below its minimum')
    return value

def coordinate_list(value,label):
    check(type(value)is list,label+' must be a list')
    for x in value:integer(x,label+' coordinate')
    return value

def signed_pairs(coords):
    return [v for x in coords for v in(max(x,0),max(-x,0))]

def term_list(terms,arity,degree,label):
    check(type(terms)is list,label+' must be a term list')
    seen=set()
    for term in terms:
        check(type(term)is list and len(term)==2,label+' term schema')
        coefficient,monomial=term
        integer(coefficient,label+' coefficient');check(coefficient!=0,label+' zero coefficient')
        check(type(monomial)is list and len(monomial)<=degree,label+' monomial degree/schema')
        for j in monomial:
            integer(j,label+' variable index',0);check(j<arity,label+' variable index out of range')
        key=tuple(monomial)
        check(monomial==sorted(monomial),label+' noncanonical monomial')
        check(key not in seen,label+' duplicate monomial');seen.add(key)

def evaluate_terms(terms,values):
    answer=0
    for coefficient,monomial in terms:
        z=coefficient
        for j in monomial:z*=values[j]
        answer+=z
    return answer

def verify(q,s,w,mutate=True):
    object_schema(q,('format','input_count','variable_count','terms'),'quartic')
    object_schema(s,('format','input_count','variable_names','residuals','ledger'),'SOS')
    object_schema(w,('input','target','values'),'witness')
    check(q['format']=='sparse-integer-polynomial-v1','quartic format')
    check(s['format']=='natural-quartic-sos-v1','SOS format')
    x=coordinate_list(w['input'],'input');y=coordinate_list(w['target'],'target')
    check(len(x)==len(y),'input and target masses disagree');n=len(x)
    qi=integer(q['input_count'],'quartic input_count',0)
    si=integer(s['input_count'],'SOS input_count',0)
    check(qi==si==4*n,'external arities disagree with signed-coordinate metadata')
    arity=integer(q['variable_count'],'quartic variable_count',0)
    values=w['values'];names=s['variable_names']
    check(type(values)is list and type(names)is list,'values/names list schema')
    check(arity==len(values)==len(names)and arity>=qi,'total arities disagree')
    check(all(type(name)is str for name in names)and len(set(names))==len(names),'variable names schema')
    for value in values:integer(value,'natural assignment',0)
    check(values[:qi]==signed_pairs(x)+signed_pairs(y),'input/target metadata differs from canonical external prefix')
    check(type(s['ledger'])is dict,'SOS ledger schema')
    term_list(q['terms'],arity,4,'quartic')
    check(type(s['residuals'])is list,'residual list schema')
    for row in s['residuals']:term_list(row,arity,2,'residual')
    expanded={}
    for row in s['residuals']:
        for a,m in row:
            for b,k in row:
                mon=tuple(sorted(m+k));expanded[mon]=expanded.get(mon,0)+a*b
    expanded={m:c for m,c in expanded.items()if c}
    ordinary={tuple(m):c for c,m in q['terms']}
    check(expanded==ordinary,'serialized quartic is not the literal SOS expansion')
    check(all(evaluate_terms(row,values)==0 for row in s['residuals']),'nonzero residual')
    check(evaluate_terms(q['terms'],values)==0,'nonzero quartic')
    mutation_count=0
    if mutate:
        # Work on a private copy so even rejected tests cannot alter caller metadata.
        changed=list(values)
        for j in range(qi,arity):
            changed[j]+=1
            check(evaluate_terms(q['terms'],changed)>0,('mutation escaped',j))
            changed[j]-=1;mutation_count+=1
    return dict(status='PASS',inputs=qi,witnesses=arity-qi,residuals=len(s['residuals']),
        quartic_monomials=len(q['terms']),positive_witness_mutations=mutation_count,
        exact_schema_checked=True,coordinate_metadata_bound=True)

def main():
    root=Path(__file__).resolve().parent
    q=json.loads((root/'example-pair-quartic.json').read_text())
    s=json.loads((root/'example-pair-sos.json').read_text())
    w=json.loads((root/'example-pair-witness.json').read_text())
    result=verify(q,s,w)
    result['polynomial_sha256']=hashlib.sha256((root/'example-pair-quartic.json').read_bytes()).hexdigest()
    print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
