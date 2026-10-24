"""Deterministic discovery of signed linear-row implications; checker is separate."""
import json,pathlib,collections,random
HERE=pathlib.Path(__file__).resolve().parent
EQ=json.loads((HERE.parent/'equations_v3/cap64/equation.json').read_text())
N=len(EQ['variables'])
ROWS=[{tuple(m):c for c,m in r['terms']} for r in EQ['residuals']]

def dependencies(poly,strict=False):
    # A certificate that the polynomial is nonnegative/positive.
    # Every square is nonnegative regardless of its base.
    if not poly:return [] if not strict else None
    if any(c<0 for m,c in poly.items() if m):return None
    constant=poly.get((),0)
    req=set()
    positive_monomials=[]
    for m,c in poly.items():
        if not m:continue
        counts=collections.Counter(m)
        req.update((v,0) for v,k in counts.items() if k%2)
        positive_monomials.append((c,set((v,1) for v in counts)))
    target=1 if strict else 0
    if constant>=target:return [(req, {'constant':constant})]
    # One positive monomial can pay a small negative constant.
    alternatives=[]
    for c,extra in positive_monomials:
        if c+constant>=target:
            alternatives.append((req|extra,{'constant':constant,'positive_monomial':sorted(extra),'coefficient':c}))
    return alternatives or None

RULES=[]
for ri,row in enumerate(ROWS):
    for v in {v for m in row for v in m}:
        if any(m.count(v)>1 for m in row):continue
        A={tuple(i for i in m if i!=v):c for m,c in row.items() if v in m}
        B={m:-c for m,c in row.items() if v not in m}
        for sign in (1,-1):
            a={m:sign*c for m,c in A.items()}
            b={m:sign*c for m,c in B.items()}
            da=dependencies(a,True)
            if not da:continue
            for strict in (False,True):
                db=dependencies(b,strict)
                if db is None:continue
                # zero right side permits >=0, including constant empty polynomial.
                if db==[]:db=[(set(),{})]
                for (ra,ca) in da:
                    for (rb,cb) in db:
                        req=ra|rb
                        if (v,int(strict)) in req:continue
                        RULES.append({'row':ri,'target':(v,int(strict)),'requires':req,'sign':sign,'a':a,'b':b})
for v in range(N):RULES.append({'row':None,'target':(v,0),'requires':{(v,1)}})

def closure(guarded,record=False):
    known={(v,0) for v in guarded};history=[]
    changed=True
    while changed:
        changed=False
        for i,r in enumerate(RULES):
            if r['target'] not in known and r['requires']<=known:
                known.add(r['target']);changed=True
                if record:history.append(i)
    return known,history

def optimize(seed=0):
    rng=random.Random(seed)
    guards=set(range(N));vs=list(range(N));rng.shuffle(vs)
    # Larger dependency impact first helps retain sources.
    for v in vs:
        known,_=closure(guards-{v})
        if all((k,0) in known for k in range(N)):guards.remove(v)
    return guards

