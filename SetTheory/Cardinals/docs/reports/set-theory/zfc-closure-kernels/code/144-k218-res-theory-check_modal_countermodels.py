#!/usr/bin/env python3
"""Check finite obstructions to proposed K/S calibration steps, without Z3.

These are models of normality, seriality and B6, not claimed models of the
complete numerical calculus or the full set-theoretic bundle. They do not
refute equiconsistency of the unfinished K/S proposal.
"""
import argparse,json
from pathlib import Path

MODELS=[
 {'name':'double_negated_persistence_is_not_persistence','above':[3,2,4],
  'Q':{0:0,2:0,3:2,4:4,6:4,7:7}},
 {'name':'Booleanized_quantifiers_need_not_commute','above':[9,6,4,8],
  'Q':{0:0,4:0,6:9,8:0,9:4,12:0,13:4,14:9,15:15},
  'R':{0:0,4:0,6:8,8:0,9:0,12:0,13:0,14:8,15:15}},
]
def need(x,msg):
    if not x:raise ValueError(msg)
def check(m):
    above=m['above'];n=len(above);top=(1<<n)-1
    need(all(a>>i&1 for i,a in enumerate(above)),'nonreflexive order')
    need(all(not(above[i]>>j&1)or above[j]&~above[i]==0 for i in range(n)for j in range(n)),'nontransitive order')
    need(all(i==j or not(above[i]>>j&1 and above[j]>>i&1) for i in range(n)for j in range(n)),'nonantisymmetric order')
    H=[a for a in range(top+1)if all(not(a>>i&1)or above[i]&a==above[i]for i in range(n))]
    def imp(a,b):return sum(1<<i for i in range(n)if above[i]&a&~b==0)
    def neg(a):return imp(a,0)
    def nn(a):return neg(neg(a))
    le=lambda a,b:a&~b==0
    for name in ('Q','R'):
        if name not in m:continue
        q=m[name];need(set(q)==set(H)and set(q.values())<=set(H),'map domain/range')
        need(q[top]==top and q[0]==0,'top preservation or seriality')
        for a in H:
            need(le(neg(q[neg(q[a])]),a),'B6')
            for b in H:
                need(q[a&b]==q[a]&q[b],'meet preservation')
                need(le(q[imp(a,b)],imp(q[a],q[b])),'normal modal implication')
    Q=m['Q'];out={'name':m['name'],'above':above,'H':H,'Q':Q,'normal_serial_B6':True}
    if 'R'not in m:
        witnesses=[{'A':a,'QA':Q[a],'nn_QA':nn(Q[a]),'nn_persistence':nn(imp(a,Q[a]))}
          for a in H if nn(imp(a,Q[a]))==top and not le(a,Q[a])and nn(Q[a])!=Q[a]]
        need(witnesses,'no persistence counterexample');out['witnesses']=witnesses
    else:
        R=m['R'];need(all(Q[R[a]]==R[Q[a]]for a in H),'original quantifiers do not commute')
        nq=lambda a:nn(Q[a]);nr=lambda a:nn(R[a])
        witnesses=[{'A':a,'nq_nr_A':nq(nr(a)),'nr_nq_A':nr(nq(a))}
          for a in H if nn(a)==a and nq(nr(a))!=nr(nq(a))]
        need(witnesses,'no Booleanization counterexample')
        out.update(R=R,original_quantifiers_commute=True,witnesses=witnesses)
    return out
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    receipt={'status':'PASS','scope':__doc__,'models':[check(m)for m in MODELS]}
    a.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','countermodels':len(receipt['models'])}))
if __name__=='__main__':main()
