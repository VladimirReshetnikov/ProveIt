import itertools,json,hashlib,platform,pathlib
MISSING=object()
def opener(a,t=MISSING,d=0,k=0):
    if isinstance(a,list):return [opener(b,t,d+5-len(a),k) for b in a]
    if type(a) is not int:raise ValueError
    if k<=a<d:return a or 1
    v=opener(t,d=3,k=k)
    return d%2*v
class Budget(Exception):pass
def term(a,slots=(),params=None,c=1,budget=None):
    params=params or {}
    if budget is None:budget=[30000]
    budget[0]-=1
    if budget[0]<0:raise Budget
    if type(a) is int:
        if 0<=a<3:return 0
        if a<0:return params[a]
        return slots[(a-3)//2]
    n=len(a)
    if n==1:return 1+term(a[0],(0,c)+slots,params,c,budget)
    if n==3:
        count=term(a[0],(0,)+slots,params,c,budget)
        value=term(a[1],(0,)+slots,params,c,budget)
        if count>100:raise Budget
        for _ in range(count):value=term(a[2],(value,)+slots,params,c,budget)
        return value
    return 0
leaves=[0,1,2,3,4,5,6,7,8,9]
small=leaves+[[],*[ [x] for x in leaves], [1,1,3],[1,3,3],[3,1,[7]],[5,1,[7]], [[1],1,3],[[1],1,[7]],[1,1,5],[1,1,7]]
counts={'attempts':0,'opened':0,'checked':0,'budget':0}
for s,u,t in itertools.product(small,repeat=3):
    if not u:continue
    counts['attempts']+=1
    try:
        r=[s,u,t]
        h=[[s and[s],u,t],opener(t,r,3) if s else u]
        h=opener(h,-1,k=-1)
        counts['opened']+=1
    except (ValueError,TypeError):continue
    try:
        lhs=term(h[0],params={-1:0})
        rhs=term(h[1],params={-1:0})
        counts['checked']+=1
    except Budget:
        counts['budget']+=1
        continue
    if lhs!=rhs:
        print('COUNTEREXAMPLE',s,u,t,h,lhs,rhs)
        break
else:
    result={
      'status':'no counterexample in the explicitly enumerated finite sample',
      'python':platform.python_version(),
      'successor_dummy_slots':[0,1],
      'iterator_dummy_slot':0,
      'administrative_parameter_values':{'-1':0},
      'sample_trees':small,
      'sampling':'all ordered triples (s,u,t) from sample_trees with truthy u',
      'counts':counts,
      'scope':'eager three-field computation-supply candidates only; not a proof of soundness',
      'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
    }
    (pathlib.Path(__file__).resolve().parents[1]/'evidence/second_dummy_computation_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('NO COUNTEREXAMPLE',counts)
