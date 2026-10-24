"""Exact scalar polynomial auditor; no builder imported."""
from collections import defaultdict

def require(ok,message):
    if not ok: raise ValueError(message)

def poly(terms):
    result={}
    for coefficient,monomial in terms:
        require(isinstance(coefficient,int) and coefficient!=0,'nonzero integer coefficient')
        m=tuple(monomial)
        require(m==tuple(sorted(m)),'canonical sorted monomial')
        require(m not in result,'unique monomial')
        result[m]=coefficient
    return result


def verify_expansion(equation,expanded):
    require(equation['domain']==expanded['domain']=='unrestricted integers',
            'unrestricted integer domain at final equation')
    n=len(equation['variables'])
    require(expanded['variables']==n,'expanded polynomial coordinate count')
    result=defaultdict(int);used=set();row_height=0
    for row in equation['residuals']:
        p=poly(row['terms'])
        require(p and max(map(len,p))<=2,'nonzero quadratic residual')
        require(all(0<=i<n for mon in p for i in mon),'coordinate bounds')
        used.update(i for mon in p for i in mon)
        row_height=max(row_height,max(map(abs,p.values())))
        for m1,c1 in p.items():
            for m2,c2 in p.items():
                result[tuple(sorted(m1+m2))]+=c1*c2
    result={m:c for m,c in result.items() if c}
    require(result==poly(expanded['terms']),'complete expanded coefficient dictionary')
    require(used==set(range(n)),'all displayed variables occur')
    metrics=dict(variables=n,quadratic_rows=len(equation['residuals']),
                 exact_degree=max(map(len,result)),expanded_monomials=len(result),
                 max_abs_expanded_coefficient=max(map(abs,result.values())),
                 max_abs_row_coefficient=row_height)
    for key,value in metrics.items():
        require(equation['metrics'][key]==value,'metric '+key)
    return metrics

