"""Connected low-width fixtures; no manifold-realization claim."""
def defect_tile(left_weight=1,right_weight=1, a=1,b=1,c=1,d=2):
    return {'inputs':[{'name':'p','side':'C'}], 'commands':[
        {'op':'introduce','name':'a','side':'R','weight':left_weight},
        {'op':'introduce','name':'b','side':'R','weight':right_weight},
        {'op':'edge','row':'a','column':'p','count':1},
        {'op':'edge','row':'b','column':'p','count':1},
        {'op':'forget','name':'p'},
        {'op':'introduce','name':'u','side':'C'},
        {'op':'edge','row':'a','column':'u','count':a},
        {'op':'edge','row':'b','column':'u','count':b},
        {'op':'forget','name':'u'},
        {'op':'introduce','name':'q','side':'C'},
        {'op':'edge','row':'a','column':'q','count':c},
        {'op':'edge','row':'b','column':'q','count':d},
        {'op':'forget','name':'a'}, {'op':'forget','name':'b'}], 'outputs':{'q':'p'}}


def path_tile(weight=1):
    return {'inputs':[{'name':'p','side':'C'}], 'commands':[
        {'op':'introduce','name':'a','side':'R','weight':weight},
        {'op':'edge','row':'a','column':'p','count':1},
        {'op':'introduce','name':'q','side':'C'},
        {'op':'edge','row':'a','column':'q','count':1},
        {'op':'forget','name':'a'}, {'op':'forget','name':'p'}],
        'outputs':{'q':'p'}}


def chain_matrix(q,weights=(1,1)):
    if type(q) is not int or q<0:raise ValueError('q must be nonnegative')
    a=[[0]*(2*q+1) for _ in range(2*q)]
    w=[]
    for i in range(q):
        for r in (2*i,2*i+1):a[r][2*i]=a[r][2*i+1]=1
        a[2*i][2*i+2]=1;a[2*i+1][2*i+2]=2
        w.extend(weights)
    return a,w


def chain_decomposition(q):
    from pivotwidth import Decomposition
    if q==0:return Decomposition((frozenset({0}),frozenset()),(1,None),1)
    m=2*q;bags=[]
    for i in range(q):
        bags.extend([frozenset({2*i,2*i+1,m+2*i}),
                     frozenset({2*i,2*i+1,m+2*i+1}),
                     frozenset({2*i,2*i+1,m+2*i+2})])
    bags.append(frozenset());parent=tuple(list(range(1,len(bags)))+[None])
    return Decomposition(tuple(bags),parent,len(bags)-1)
