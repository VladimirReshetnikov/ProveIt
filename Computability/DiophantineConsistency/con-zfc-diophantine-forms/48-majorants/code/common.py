from pathlib import Path
from functools import lru_cache
import json,math,gzip,hashlib
from collections import Counter
from circuit import Circuit
from sparse_arithmetic import add,mul,shift_positive
ROOT=Path(__file__).resolve().parents[1]
PORTS=['beta','K0','MC','MF']; PORT_FILES=['beta','K','MC','MF_source']
ROW_ORDER=list(range(4))+list(range(5,22))+[4]
BETA_EXPONENT=2140030
class DAG(Circuit):
 const=Circuit.c; plus=Circuit.add; times=Circuit.mul; minus=Circuit.sub; power=Circuit.pow; prune=Circuit.export
 def var(self,n):return self.node('variable',n)
 def fixed(self,n):return self.node('fixed',n)
def read_ports():
 return {n:int.from_bytes(gzip.decompress((ROOT/'data/ports'/f'{f}.bin.gz').read_bytes()),'little') for n,f in zip(PORTS,PORT_FILES)}
def parent_rows():
    data=json.loads((ROOT/'data/parent_system.json').read_text())
    names=data['variables']+data['constants']; n=len(data['variables'])
    z=(0,)*len(names)
    env={}
    for i,name in enumerate(names):
        ex=list(z);ex[i]=1;env[name]={tuple(ex):1}
    def read(v):return ({z:v} if v else {}) if isinstance(v,int) else env[v]
    for name,op,a,b in data['source']:
        env[name]=mul(read(a),read(b)) if op=='*' else add(read(a),read(b),-1 if op=='-' else 1)
    raw=[shift_positive(add(read(a),read(b),-1),n) for a,b in data['comparisons']]
    assert len(raw)==22 and n==31
    return [raw[i] for i in ROW_ORDER],data['variables']


def coefficient_data():
    rows,names=parent_rows(); records=[]; aliases={}; recipes={}; n=len(names)
    for j,row in enumerate(rows):
        grouped={}
        for mon,coef in row.items():
            alpha,ports=mon[:n],mon[n:]
            d=sum(alpha);assert d<=2
            multiplier=math.factorial(2-d)*math.prod(math.factorial(x) for x in alpha)
            grouped.setdefault(alpha,{})[ports]=coef*multiplier
        rec=[]
        for alpha,poly in sorted(grouped.items()):
            poly={p:c for p,c in poly.items() if c}
            signature=tuple(sorted(poly.items()))
            if len(signature)==1 and not any(signature[0][0]):
                leaf=signature[0][1]; sign=1
            else:
                sign=1 if signature[0][1]>0 else -1
                signature=tuple((p,c*sign) for p,c in signature)
                if signature not in aliases:
                    name=f'c{len(aliases):03d}'
                    aliases[signature]=name
                    recipes[name]=[{'powers':list(p),'coefficient':c} for p,c in signature]
                leaf=aliases[signature]
            rec.append({'alpha':list(alpha),'leaf':leaf,'sign':sign})
        records.append(rec)
    return {'variables':names,'ports':PORTS,'row_order_one_based':[i+1 for i in ROW_ORDER],
            'rows':records,'recipes':recipes,'beta_source_exponent':BETA_EXPONENT}


def evaluate_recipe(recipe,ports,modulus=None):
    total=0
    for row in recipe:
        term=row['coefficient']
        for name,power in zip(PORTS,row['powers']):
            term*=pow(ports[name],power,modulus) if modulus else ports[name]**power
            if modulus:term%=modulus
        total+=term
    return total%modulus if modulus else total


def fixed_values(data,modulus):
    ports=read_ports()
    result={name:evaluate_recipe(poly,ports,modulus) for name,poly in data['recipes'].items()}
    result['beta_source']=pow(2,BETA_EXPONENT,modulus)
    return result


def geometric_pair(d,base,n):
    if n==0:return d.const(1),d.const(0)
    if n==1:return base,d.const(1)
    p,s=geometric_pair(d,base,n//2)
    p2=d.times(p,p);s2=d.times(s,d.plus(d.const(1),p))
    return (d.times(p2,base),d.plus(s2,p2)) if n%2 else (p2,s2)


def quadratic_form(d,terms,coordinates):
    """Shared multivariate Horner evaluation, with a fixed degree of two."""
    @lru_cache(None)
    def go(items):
        if not items:return d.const(0)
        counts=[sum(ex[j]>0 for ex,co in items) for j in range(len(coordinates))]
        if not max(counts):return d.plus(*(co for ex,co in items))
        j=max(range(len(coordinates)),key=lambda j:(counts[j],sum(ex[j] for ex,co in items),j))
        yes=[];no=[]
        for ex,co in items:
            if ex[j]:
                e=list(ex);e[j]-=1;yes.append((tuple(e),co))
            else:no.append((ex,co))
        return d.plus(go(tuple(no)),d.times(coordinates[j],go(tuple(yes))))
    return go(tuple(terms))


