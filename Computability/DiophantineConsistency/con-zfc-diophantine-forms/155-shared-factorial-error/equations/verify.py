#!/usr/bin/env python3
"""Independent exact audit of the 250-integer composition; no builder import."""
import copy,hashlib,json,sys
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def need(b,m):
    if not b:raise ValueError(m)
def sparse(terms):
    d=Counter()
    for c,m in terms:
        need(isinstance(c,int) and c!=0,'Invalid coefficient')
        need(m==sorted(m),'Noncanonical monomial')
        d[tuple(m)]+=c
    return {m:c for m,c in d.items() if c}
def check(eq,poly,meta,cert,parent):
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    deleted={names['new_guard2.'+x] for x in 'abc'}
    keep=[j for j in range(len(parent['variables'])) if j not in deleted]
    ren={j:i for i,j in enumerate(keep)}
    need(cert['removed_variables']==sorted(deleted),'Wrong deleted variables')
    need(cert['kept_parent_coordinates']==keep,'Wrong coordinate injection')
    rows=[i for i,r in enumerate(parent['residuals']) if r['label']=='domain_guard.2']
    need(len(rows)==1 and cert['removed_row']==rows[0],'Wrong deleted row')
    old=rows[0]
    a,b,c=sorted(deleted);q=names['pow2.output'];B=names['choose0.output']
    need(sparse(parent['residuals'][old]['terms'])=={():-2,(B,):-1,(q,):1,(a,a):-1,(b,b):-1,(c,):-1,(c,c):-1},'Wrong inherited output guard')
    expected=[]
    for i,r in enumerate(parent['residuals']):
        if i==old:continue
        need(not any(v in deleted for _,m in r['terms'] for v in m),'Witness is nonprivate')
        expected.append({'label':r['label'],'terms':[[a,[ren[v] for v in m]] for a,m in r['terms']]})
    z=len(keep)
    expected.append({'label':'radix.odd_square','terms':[[-2,[]],[1,[ren[q]]],[-4,[z]],[-4,[z,z]]]})
    need(eq['residuals']==expected,'Residual list or odd-square identity mismatch')
    vars=[parent['variables'][i] for i in keep]+[{'kind':'integer_witness','name':'radix.odd_square_root_half'}]
    need(eq['variables']==vars,'Variables differ')
    need(cert['new_coordinate']==z and cert['q_parent_coordinate']==q and cert['q_parent_shift']==-1,'Shift or coordinate record differs')
    acc=Counter()
    for r in eq['residuals']:
        terms=list(sparse(r['terms']).items())
        need(all(len(m)<=2 for m,c in terms),'Nonquadratic residual')
        for i,(m,c) in enumerate(terms):
            acc[tuple(sorted(m+m))]+=c*c
            for n,d in terms[i+1:]:acc[tuple(sorted(m+n))]+=2*c*d
    collected={m:c for m,c in acc.items() if c}
    need(sparse(poly['terms'])==collected,'Collected polynomial mismatch')
    need(poly['variable_count']==len(vars) and poly['domain']=='Z','Polynomial domain/count mismatch')
    live={v for m in collected for v in m}
    need(live==set(range(len(vars))),'Inactive coordinate')
    actual={'variables':len(vars),'rows':len(expected),'degree':max(map(len,collected)),'monomials':len(collected),'height':max(map(abs,collected.values())),'row_height':max(abs(c) for r in expected for c,m in r['terms'])}
    need(meta==actual,'Metrics mismatch')
    need(actual=={'variables':250,'rows':182,'degree':4,'monomials':5324,'height':128446,'row_height':256},'Unexpected endpoint')
    return actual
def main():
    p=ROOT/'parent252/equation/equation.json';parent=json.loads(p.read_text());base=ROOT/'equation250'
    eq=json.loads((base/'equation.json').read_text());poly=json.loads((base/'expanded_polynomial.json').read_text());meta=json.loads((base/'METRICS.json').read_text());cert=json.loads((base/'transformation.json').read_text())
    need(cert['parent_sha256']==hashlib.sha256(p.read_bytes()).hexdigest(),'Parent hash mismatch')
    need(eq['parent_equation_sha256']==cert['parent_sha256'],'Equation parent hash mismatch')
    actual=check(eq,poly,meta,cert,parent)
    tests=[]
    mutations=[]
    ee=copy.deepcopy(eq);ee['residuals'][-1]['terms'][0][0]=-1;mutations.append(('missing q translation',ee,poly,meta,cert))
    ee=copy.deepcopy(eq);ee['residuals'][-1]['terms'][-1][0]=-1;mutations.append(('wrong square coefficient',ee,poly,meta,cert))
    ee=copy.deepcopy(eq);ee['residuals'].pop(5);mutations.append(('missing retained residual',ee,poly,meta,cert))
    pp=copy.deepcopy(poly);pp['terms'][10][0]+=1;mutations.append(('quartic coefficient corruption',eq,pp,meta,cert))
    cc=copy.deepcopy(cert);cc['q_parent_shift']=0;mutations.append(('wrong semantic shift',eq,poly,meta,cc))
    for name,ee,pp,mm,cc in mutations:
        try:check(ee,pp,mm,cc,parent)
        except ValueError:tests.append(name)
        else:raise ValueError('Corruption accepted: '+name)
    print(json.dumps({'status':'PASS','optimized':bool(sys.flags.optimize),'metrics':actual,'rejected_controls':tests,'scope':'Finite exact transformation and complete coefficient audit; semantic proof is separate.'},indent=2))
if __name__=='__main__':main()
