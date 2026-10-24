#!/usr/bin/env python3
"""Independent exact source-substitution and sextic audit. No CAS needed.

This checker does not import or execute the builder. All polynomial identities
are checked in the free integer polynomial ring including the four coefficient
ports. It does not reprove the inherited native compiler theorem.
"""
from pathlib import Path
import ast
import hashlib
import json

ROOT=Path(__file__).resolve().parent

def need(ok, message):
    if not ok:
        raise ValueError(message)

class Ring:
    def __init__(self,names):
        self.names=names
        self.index={x:i for i,x in enumerate(names)}
        self.one=(0,)*len(names)
    def scalar(self,n):
        return {self.one:n} if n else {}
    def variable(self,x):
        p=list(self.one);p[self.index[x]]=1
        return {tuple(p):1}
    def add(self,a,b,sign=1):
        c=a.copy()
        for m,v in b.items():
            c[m]=c.get(m,0)+sign*v
            if not c[m]:del c[m]
        return c
    def multiply(self,a,b):
        c={}
        for i,x in a.items():
            for j,y in b.items():
                k=tuple(u+v for u,v in zip(i,j))
                c[k]=c.get(k,0)+x*y
                if not c[k]:del c[k]
        return c
    def power(self,a,n):
        r=self.scalar(1)
        while n:
            if n&1:r=self.multiply(r,a)
            n//=2
            if n:a=self.multiply(a,a)
        return r
    def read(self,s,env=None):
        env=env or {}
        def rec(t):
            if isinstance(t,ast.Constant) and type(t.value) is int:
                return self.scalar(t.value)
            if isinstance(t,ast.Name):
                return env[t.id] if t.id in env else self.variable(t.id)
            if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):
                return {m:-c for m,c in rec(t.operand).items()}
            if isinstance(t,ast.BinOp):
                if isinstance(t.op,ast.Add):return self.add(rec(t.left),rec(t.right))
                if isinstance(t.op,ast.Sub):return self.add(rec(t.left),rec(t.right),-1)
                if isinstance(t.op,ast.Mult):return self.multiply(rec(t.left),rec(t.right))
                if isinstance(t.op,ast.Pow):
                    need(isinstance(t.right,ast.Constant) and type(t.right.value) is int and 0<=t.right.value<=8,'bounded fixed exponent')
                    return self.power(rec(t.left),t.right.value)
            raise ValueError('not polynomial syntax: '+ast.dump(t))
        return rec(ast.parse(s,mode='eval').body)

def main():
    obj=json.loads((ROOT/'sextic34.json').read_text())
    raw=(ROOT/obj['source']['local_path']).read_bytes()
    git=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    need(git==obj['source']['git_blob_sha1'],'authentic Q41 source identity')
    source=json.loads(raw)
    need(source['variable_count']==41 and source['equation_count']==26,'Q41 dimensions')
    vs=obj['variables'];ports=obj['fixed_numerals'];ring=Ring(vs+ports)
    need(len(vs)==34 and len(set(vs))==34,'exactly34 distinct unknowns')
    need(ports==['beta','K0','MC','MF'],'fixed numeral ports')

    # These formulas are independently specified, not read from the candidate's
    # restoration field. Source positivity witnesses are reselected separately.
    q='(beta*J+1)'
    restoredF=f'((K0+4*w_scale)*C-z*({q}-1))'
    substitutions={
      'F':restoredF,'alpha':f'{q}-{restoredF}-C',
      'L':f'{q}**2-1','X':'2*u**2','C2':'c**2','F2':'f**2',
      'g':'y**2-V**2','P':'eta+zeta+E*(c-eta)',
      'tau':'tau_gap+E*(c-eta)',
      'FA_pos1':'CA_pos1','FA_pos2':'CA_pos2','FA_pos3':'CA_pos3'}
    env={x:ring.read(expr) for x,expr in substitutions.items()}
    changed=list(source['residuals'])
    need(changed[23]=='F*alpha-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)-1','source Falpha guard')
    changed[23]='(beta*J+1-F-alpha)*alpha-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)-1'
    deleted=[0,6,10,13,14,17,22]
    source_residuals=[ring.read(s,env) for s in changed]
    for i in deleted:
        need(not source_residuals[i],f'deleted definition {i} vanishes identically')
    kept=[p for i,p in enumerate(source_residuals) if i not in deleted]
    actual=[ring.read(s) for s in obj['residuals']]
    need(len(kept)==len(actual)==19,'nineteen residuals')
    for n,(a,b) in enumerate(zip(kept,actual)):
        need(a==b,f'complete independent restoration of residual {n}')

    # Check the inverse coordinate change in the source free polynomial ring.
    old=Ring(source['variables']+ports)
    cOld='(beta*J+1-F-alpha)'
    oldtau=old.read('tau-E*(c-eta)')
    need(old.add(oldtau,old.read('E*(c-eta)'))==old.read('tau'),'inverse tau shift')
    need(old.read(f'beta*J+1-F-{cOld}')==old.read('alpha'),'inverse complement shift')
    need(old.read(f'(K0+4*w_scale)*{cOld}-z*(beta*J)-F')==old.read(source['residuals'][13]),'transport eliminates F monically')

    degrees=[max((sum(m[:34]) for m in p),default=-1) for p in actual]
    need(all(d<=3 for d in degrees),'all residuals cubic or lower')
    total={}
    for p in actual:total=ring.add(total,ring.multiply(p,p))
    need(max(sum(m[:34]) for m in total)==6,'exact sextic total degree')
    mon=[0]*len(ring.names);mon[ring.index['r']]=2;mon[ring.index['c']]=4
    need(total.get(tuple(mon))==4,'uniform degree certificate r²c⁴=4')
    live={vs[j] for p in actual for m in p for j in range(34) if m[j]}
    need(live==set(vs),'all unknowns live')
    # Exhaustive sign table checks the elementary guard equivalence. The proof
    # for arbitrary integers uses only sign and nonzero status, not magnitudes.
    for F in (-1,0,1):
        for C in (-1,0,1):
            for a in (-1,0,1):
                need((F*a>0 and F*C>0)==(C*a>0 and F*C>0),'common-sign truth table')
    receipt={
      'status':'PASS','source_git_blob':git,'unknowns':34,'residuals':19,
      'residual_degrees':degrees,'exact_sos_degree':6,
      'degree_certificate':{'monomial':'r^2*c^4','coefficient':4},
      'symbolic_sos_monomials':len(total),'all_unknowns_live':True,
      'deleted_source_rows_zero_based':deleted,
      'source_restoration_identities':26,'inverse_affine_identities':2,
      'common_sign_table_cases':27,
      'scope':'Exact identities, dimensions and degree; written positivity and inherited source theorem establish semantic equivalence.'}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    expansion=[{'coefficient':c,'powers':{ring.names[i]:e for i,e in enumerate(m) if e}}
               for m,c in sorted(total.items())]
    (ROOT/'sextic34_expanded.json').write_text(json.dumps(expansion,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
