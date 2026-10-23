from pathlib import Path
import sys, json, random
from copy import deepcopy
sys.path.insert(0,str(Path(__file__).parents[1]/'vendor/norm21'))
import build_norm12 as base
HERE=Path(__file__).resolve().parents[1]/'circuits'

def construct():
    ps=base.construct()
    for p in ps:
        s=[]
        for row in p['source']:
            n=row[0]
            if n=='Qr':
                s.extend([['I','*','i','c2'],['I2','*','I','I'],['Dm1','*','Delta','I2'],['D','+','Dm1',1],['Q','*','Delta','Dm1']])
            elif n in ['Q','I','Dm1','D']:continue
            elif n=='v':s.append(['T2','*','T','T'])
            elif n=='v2':s.append(['v2','*','c2','T2'])
            elif n=='bound0':
                s.extend([['XI2','*','X','I2'],['Bnd','+','T2','XI2']])
            elif n in ['bound1','Bnd']:continue
            elif n=='HL2':
                s.extend([['taucoef','*',4,'HBnd'],['HL2','*','taucoef','taucoef']])
            else:s.append(row)
        p['source']=s;p['name']=p['name'].replace('norm12','compact12')
        if 'output' in p:p['exact_degree']=1081 if p['output']=='polynomial' else 2144
        else:p['residual_exact_degrees']=[7,2,1072]
        base.ledger(p)
    return ps

def independent_norm(a):
    G,A,D=a['G'],a['A'],a['D']
    def product(x,y):
        z=[0]*8
        for i,v in enumerate(x):
            for j,w in enumerate(y):
                fact=1
                if i&j&1:fact*=G
                if i&j&2:fact*=A
                if i&j&4:fact*=D
                z[i^j]+=fact*v*w
        return z
    B=2*a['Q']*a['c']*a['T']*a['b'];acc=[1]+[0]*7
    for su in (-1,1):
      for st in (-1,1):
       for sf in (-1,1):
        root=[a['S'],-su*a['L'],-st*a['taucoef'],0,0,0,0,0]
        w=[a['d']*x for x in product(root,root)]
        w[0]-=a['H']**2*a['e'];w[4]+=sf*a['H']**2*B
        acc=product(acc,w)
    assert not any(acc[1:])
    return acc[0]

if __name__=='__main__':
    ps=construct();rng=random.Random(1081)
    for _ in range(24):
        v={n:rng.randrange(-2,4) for n in base.WITNESSES+base.FIXED}
        a=base.evaluate(ps[0],v)
        assert a['N']==independent_norm(a)
        assert a['N1']%8==0
        assert (a['N']-a['N0']**2)%64==0
    d=base.ledger(ps[0]);print({n:d[n] for n in ['I2','Bnd','L','taucoef','a0','V0','V1','C0','C1','N0','N1','N']})
    for p in ps:
        (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        print(p['name'],p['ledger'])
