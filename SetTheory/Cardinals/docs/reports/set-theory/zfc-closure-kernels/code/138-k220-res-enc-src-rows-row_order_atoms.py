#!/usr/bin/env python3
"""Exact logical-row reorderings on the original closed-block concatenation shape.

Every moved atom has boundary (0,0,False), so its internal guarded control
flow is unchanged and it returns normally.  The surrounding concatenation
tree may be retained while substituting the reordered list of atom roots.
This preserves all per-row primitive words and the single rho8 u-reader.
"""
from pathlib import Path
from functools import cache
import itertools,json,time,collections,argparse
import search as z

OUT=z.HERE/'row_orders'
OUT.mkdir(exist_ok=True)
NAMES=list(z.INTERVALS)
VALUES=[];IDS={};META=[];BOUND=[]
def intern(x):
    if x in IDS:return IDS[x]
    k=len(VALUES);IDS[x]=k;VALUES.append(x)
    if isinstance(x[0],str):
        META.append((1,0,0,0));BOUND.append(z.s.boundary(x))
    else:
        a,b=x;al,alead,az,ah=META[a];bl,blead,bz,bh=META[b]
        lead=1+alead;META.append((al+bl,lead,max(lead,az,bz),1+max(ah,bh)))
        aa,bb=BOUND[a],BOUND[b]
        BOUND.append((max(max(aa[0]-1,0),bb[0]),max(aa[1],max(bb[1]-1,0)),aa[2]or bb[2]))
    return k

@cache
def encode(t):return intern(t)if z.s.leaf(t)else intern(tuple(map(encode,t)))

ROOT=encode(z.TREE)
assert len(VALUES)==208
ATOMS=[]
def make_template(k,lo=0):
    hi=lo+META[k][0];x=VALUES[k]
    if hi<=135 or lo>=2650:return ('F',k)
    if 135<=lo and hi<=2650 and BOUND[k]==(0,0,False):
        if isinstance(x[0],str)or any(BOUND[c]!=(0,0,False)for c in x):
            i=len(ATOMS);ATOMS.append((lo,hi,k));return ('A',i)
    assert not isinstance(x[0],str),(lo,hi,x,BOUND[k])
    return ('N',make_template(x[0],lo),make_template(x[1],lo+META[x[0]][0]))

TEMPLATE=make_template(ROOT)
ROW_ATOMS=[]
for name in NAMES:
    lo,hi=z.INTERVALS[name]
    row=[k for a,b,k in ATOMS if lo<=a and b<=hi]
    assert sum(META[k][0]for k in row)==hi-lo,name
    ROW_ATOMS.append(row)
assert sum(map(len,ROW_ATOMS))==len(ATOMS)
BASE_VALUES=list(VALUES);BASE_IDS=dict(IDS);BASE_META=list(META);BASE_BOUND=list(BOUND)

def reset():
    VALUES[:]=BASE_VALUES;IDS.clear();IDS.update(BASE_IDS)
    META[:]=BASE_META;BOUND[:]=BASE_BOUND

def compose(template,atoms):
    if template[0]=='F':return template[1]
    if template[0]=='A':return atoms[template[1]]
    return intern((compose(template[1],atoms),compose(template[2],atoms)))

def live(k):
    seen={k};todo=[k]
    for q in todo:
        x=VALUES[q]
        if isinstance(x[0],str):continue
        for c in x:
            if c not in seen:seen.add(c);todo.append(c)
    return seen

def decode(k):
    x=VALUES[k]
    return x if isinstance(x[0],str)else tuple(map(decode,x))

def candidate(order,save=False):
    atoms=sum((ROW_ATOMS[i]for i in order),[])
    q=compose(TEMPLATE,atoms);met={'dag_nodes':len(live(q)),
        'leaf_occurrences':META[q][0],'maximum_zero_run':META[q][2],'maximum_depth':META[q][3]}
    result={'order':[NAMES[i]for i in order],'order_indices':order,'source_metrics':met}
    if save:
        tt=decode(q);rr=z.s.sites(tt)
        expected=z.flat(z.TREE)[:135]+sum((tuple(tuple(r[1:])for r in z.ROWS[slice(*z.INTERVALS[NAMES[i]])])for i in order),())+z.flat(z.TREE)[2650:]
        assert z.flat(tt)==expected
        assert z.s.metrics(tt)==met
        assert z.s.graph_arithmetic(rr)[0]==z.s.graph_intervals(rr)
        d=OUT/('_'.join(map(str,order)));d.mkdir(exist_ok=True)
        (d/'sites.json').write_bytes(z.s.compact(rr))
        try:
            U,m=z.compile_tree(z.T,z.TREE,tt);result['compiler']=m
            (d/'candidate.tm').write_bytes(z.b.table_bytes(U))
        except Exception as e:result['error']=repr(e)
        (d/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def main():
    started=time.monotonic()
    (OUT/'closed_atom_binding.json').write_text(json.dumps({
        'status':'CLOSED_AX_ATOM_BINDING','interval':[135,2650],
        'row_intervals':z.INTERVALS,'atoms':ATOMS,'row_atom_counts':dict(zip(NAMES,map(len,ROW_ATOMS))),
        'every_atom_boundary':[0,0,False],'rho8_u_reader_remains_in_row':True},indent=2)+'\n')
    identity=candidate(tuple(range(8)),save=True)
    assert identity['compiler']['working_states']==221
    print('identity',json.dumps(identity),'atoms',len(ATOMS),'rows',list(map(len,ROW_ATOMS)),flush=True)
    hist=collections.Counter();best=208;bestvalid=208;records=[]
    for i,order in enumerate(itertools.permutations(range(8))):
        result=candidate(order);m=result['source_metrics'];hist[m['dag_nodes'],m['maximum_zero_run']]+=1
        if m['dag_nodes']<best or(m['maximum_zero_run']<=6 and m['dag_nodes']<bestvalid):
            result=candidate(order,save=True);records.append(result)
            best=min(best,m['dag_nodes'])
            if m['maximum_zero_run']<=6:bestvalid=min(bestvalid,m['dag_nodes'])
            print('improvement',json.dumps(result),flush=True)
        elif m['dag_nodes']<=208 and m['maximum_zero_run']<=6 and order!=tuple(range(8)):
            result=candidate(order,save=True);records.append(result);print('tie',json.dumps(result),flush=True)
        if len(VALUES)>200000:reset()
        if i and i%5000==0:print('progress',i,'best',best,'best_zero6',bestvalid,'seconds',time.monotonic()-started,flush=True)
    result={'status':'EXHAUSTIVE_FIXED_CLOSED_ATOM_SHAPE_ROW_ORDER_COMPLETE',
        'row_orders':40320,'minimum_dag_nodes':best,'minimum_dag_nodes_at_zero6':bestvalid,
        'records':records,'histogram':[[a,b,n]for(a,b),n in sorted(hist.items())],
        'seconds':time.monotonic()-started}
    (OUT/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print('complete',json.dumps(result),flush=True)

if __name__=='__main__':main()
