"""Paid integer linear forms, with repeated coefficients and shared terms.

All rewrites are polynomial identities on arbitrary integer inputs.  This
module makes no selector, one-hot, history, or positive-domain assumption.
"""

MODES=('flat','grouped','grouped_equal','grouped_minabs','grouped_first','grouped_second')


def emit(g, forms, mode='grouped_equal'):
    """Emit two forms using a paid DAG; return their output registers.

    Each form is {'coefficients':{variable:integer}, 'constant':integer}.
    Existing DAG registers may be reused, but no new computed value is free.
    """
    assert mode in MODES and len(forms)==2
    rows=[{n:c for n,c in form['coefficients'].items() if c} for form in forms]
    assert all(isinstance(c,int) for row in rows for c in row.values())
    common={}
    if mode.startswith('grouped_'):
        for n,a in rows[0].items():
            if n not in rows[1]:continue
            b=rows[1][n]
            if mode=='grouped_equal':c=a if a==b else 0
            elif mode=='grouped_minabs':c=min((a,b),key=abs) if a*b>0 else 0
            elif mode=='grouped_first':c=a
            elif mode=='grouped_second':c=b
            else:raise AssertionError(mode)
            if c:common[n]=c
    def weighted(row):
        if mode=='flat':return g.total([g.mul(c,n,'linear_coefficient') for n,c in row.items()], 'linear_sum')
        groups={}
        for n,c in row.items():
            if c:groups.setdefault(c,[]).append(n)
        terms=[g.mul(c,g.total(names,'linear_group'),'linear_coefficient')
               for c,names in groups.items()]
        return g.total(terms,'linear_sum')
    shared=weighted(common)
    answer=[]
    for row,form in zip(rows,forms):
        rest={n:c-common.get(n,0) for n,c in row.items()}
        value=g.add(shared,weighted(rest),'linear_shared_sum')
        constant=form.get('constant',0)
        assert isinstance(constant,int)
        value=(g.sub(value,-constant,'linear_constant') if constant<0
               else g.add(value,constant,'linear_constant'))
        answer.append(value)
    return answer
