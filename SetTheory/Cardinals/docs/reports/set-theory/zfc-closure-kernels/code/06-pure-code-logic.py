"""Executable reference for Q_subset: not a formally verified TM compiler.

Primitive formula tuples: (0,x,y)=membership; (1,A)=not; (2,A,B)=implies;
(3,x,A)=forall. JSON uses corresponding arrays. Integers are never booleans.
"""
from __future__ import annotations
from typing import Any

Formula = tuple

def nat(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError('expected a nonnegative integer, not a Boolean')
    return x

def formula(raw: Any) -> Formula:
    if not isinstance(raw, (list, tuple)) or not raw:
        raise ValueError('formula must be a nonempty array')
    tag = nat(raw[0])
    if tag == 0 and len(raw) == 3:
        return E(nat(raw[1]), nat(raw[2]))
    if tag == 1 and len(raw) == 2:
        return Not(formula(raw[1]))
    if tag == 2 and len(raw) == 3:
        return Imp(formula(raw[1]), formula(raw[2]))
    if tag == 3 and len(raw) == 3:
        return All(nat(raw[1]), formula(raw[2]))
    raise ValueError('unknown tag or incorrect formula arity')

def E(x: int, y: int) -> Formula: return (0, x, y)
def Not(a: Formula) -> Formula: return (1, a)
def Imp(a: Formula, b: Formula) -> Formula: return (2, a, b)
def All(x: int, a: Formula) -> Formula: return (3, x, a)
def Exists(x: int, a: Formula) -> Formula: return Not(All(x, Not(a)))
def And(a: Formula, b: Formula) -> Formula: return Not(Imp(a, Not(b)))
def Or(a: Formula, b: Formula) -> Formula: return Imp(Not(a), b)
def Iff(a: Formula, b: Formula) -> Formula: return And(Imp(a,b), Imp(b,a))
def Sub(x: int, y: int, z: int) -> Formula: return All(z, Imp(E(z,x),E(z,y)))
def D(x: int, y: int, z: int) -> Formula: return All(z,Iff(E(z,x),E(z,y)))

def variables(a: Formula) -> set[int]:
    if a[0] == 0: return {a[1],a[2]}
    if a[0] == 1: return variables(a[1])
    if a[0] == 2: return variables(a[1]) | variables(a[2])
    return {a[1]} | variables(a[2])

def free(a: Formula) -> set[int]:
    if a[0] == 0: return {a[1],a[2]}
    if a[0] == 1: return free(a[1])
    if a[0] == 2: return free(a[1]) | free(a[2])
    return free(a[2]) - {a[1]}

def rename_free(a: Formula, mapping: dict[int,int]) -> Formula:
    """Simultaneous renaming, with capture-avoiding freshening."""
    if a[0] == 0:
        return E(mapping.get(a[1],a[1]),mapping.get(a[2],a[2]))
    if a[0] == 1: return Not(rename_free(a[1],mapping))
    if a[0] == 2: return Imp(rename_free(a[1],mapping),rename_free(a[2],mapping))
    x, body = a[1], a[2]
    active = {k:v for k,v in mapping.items() if k != x and k in free(body)}
    if x in active.values():
        fresh = max(variables(body) | set(mapping) | set(mapping.values()) | {x})+1
        body = rename_free(body,{x:fresh})
        x = fresh
    return All(x,rename_free(body,active))

def alpha_key(a: Formula, bound: tuple[int,...] = ()) -> tuple:
    def var(x: int) -> tuple:
        try: return ('b',bound.index(x))
        except ValueError: return ('f',x)
    if a[0] == 0: return (0,var(a[1]),var(a[2]))
    if a[0] == 1: return (1,alpha_key(a[1],bound))
    if a[0] == 2: return (2,alpha_key(a[1],bound),alpha_key(a[2],bound))
    return (3,alpha_key(a[2],(a[1],)+bound))

def same(a: Formula,b: Formula) -> bool: return alpha_key(a)==alpha_key(b)

def ec() -> Formula:
    return All(0,All(1,Imp(D(0,1,2),All(3,Iff(E(0,3),E(1,3))))))

def schema(matrix: Formula) -> Formula:
    """Pure subset bound and subset seed. Free slots 0=input, 1=output.

    All other free variables become universally closed parameters. Every
    auxiliary binder is fresh for ALL variable labels in the source matrix.
    No test of the semantic boundedness antecedent is performed.
    """
    m = formula(matrix)
    x,b,y,a,c,z = range(max(variables(m)|{0,1})+1,max(variables(m)|{0,1})+7)
    r = rename_free(m,{0:x,1:y})
    premise = All(x,Exists(b,All(y,Imp(r,Sub(y,b,z)))))
    closure = All(x,All(y,Imp(And(Or(Sub(x,a,z),E(x,c)),r),E(y,c))))
    purity = All(y,Imp(E(y,c),Exists(x,r)))
    out = Imp(premise,All(a,Exists(c,And(closure,purity))))
    for p in sorted(free(m)-{0,1},reverse=True): out = All(p,out)
    assert not free(out)
    return out

BOTTOM = Not(All(0,Imp(E(0,0),E(0,0))))

# Record tags: L1,L2,L3,Q1,Q2,MP,GEN,EC,SC,ALPHA.
ARITIES = (3,4,3,4,4,3,3,1,2,3)

def derive(records: Any) -> list[Formula]:
    """Generate conclusions, never trust supplied conclusions or assumptions.

    Raises ValueError for a malformed or incorrect certificate. Resource
    failures are NOT invalid-certificate verdicts and are not suppressed.
    """
    if not isinstance(records,list) or not records:
        raise ValueError('certificate must be a nonempty array of records')
    lines: list[Formula] = []
    def ref(i: Any) -> Formula:
        i = nat(i)
        if i >= len(lines): raise ValueError('reference is not strictly backward')
        return lines[i]
    for rec in records:
        if not isinstance(rec,list) or not rec: raise ValueError('invalid record')
        tag = nat(rec[0])
        if tag >= len(ARITIES) or len(rec)!=ARITIES[tag]:
            raise ValueError('unknown record or wrong arity')
        if tag == 0:
            a,b = map(formula,rec[1:]); out=Imp(a,Imp(b,a))
        elif tag == 1:
            a,b,c = map(formula,rec[1:]); out=Imp(Imp(a,Imp(b,c)),Imp(Imp(a,b),Imp(a,c)))
        elif tag == 2:
            a,b = map(formula,rec[1:]); out=Imp(Imp(Not(a),Not(b)),Imp(b,a))
        elif tag == 3:
            x,y=nat(rec[1]),nat(rec[2]); a=formula(rec[3])
            out=Imp(All(x,a),rename_free(a,{x:y}))
        elif tag == 4:
            x=nat(rec[1]); a,b=map(formula,rec[2:])
            if x in free(a): raise ValueError('Q2 freshness condition fails')
            out=Imp(All(x,Imp(a,b)),Imp(a,All(x,b)))
        elif tag == 5:
            a,ab=ref(rec[1]),ref(rec[2])
            if ab[0]!=2 or not same(a,ab[1]): raise ValueError('MP mismatch')
            out=ab[2]
        elif tag == 6: out=All(nat(rec[1]),ref(rec[2]))
        elif tag == 7: out=ec()
        elif tag == 8: out=schema(formula(rec[1]))
        else:
            old,new=ref(rec[1]),formula(rec[2])
            if not same(old,new): raise ValueError('ALPHA mismatch')
            out=new
        lines.append(out)
    return lines

def check(records: Any) -> dict[str, Any]:
    try: lines=derive(records)
    except ValueError as e: return {'valid':False,'refutation':False,'error':str(e)}
    return {'valid':True,'refutation':same(lines[-1],BOTTOM),'lines':len(lines)}

def evaluate(a: Formula, domain: range, membership: set[tuple[int,int]],
             env: dict[int,int]) -> bool:
    if a[0]==0: return (env[a[1]],env[a[2]]) in membership
    if a[0]==1: return not evaluate(a[1],domain,membership,env)
    if a[0]==2:
        return not evaluate(a[1],domain,membership,env) or evaluate(a[2],domain,membership,env)
    return all(evaluate(a[2],domain,membership,env|{a[1]:v}) for v in domain)

if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',type=Path)
    args=p.parse_args()
    print(json.dumps(check(json.loads(args.certificate.read_text())),indent=2))
