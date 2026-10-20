"""Own literal tree/CFG census; no delivered executable imports or machine runs."""
from pathlib import Path
import argparse, hashlib, json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--packet',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args(); src=a.packet.resolve(); out=a.output.resolve(); out.mkdir(exist_ok=False)
def desc(p): return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def leaf(t): return isinstance(t[0],str)
def tree(rows):
    d={p:(op,n) for p,op,n in rows}; assert len(d)==len(rows)
    assert list(d)==sorted(d)
    nodes=dict(d)
    for p in sorted({p[:i] for p in d for i in range(len(p))},key=len,reverse=True):
        assert p not in d and p+'0' in nodes and p+'1' in nodes
        nodes[p]=(nodes[p+'0'],nodes[p+'1'])
    return nodes['']
def flat(t,p=''):
    return [[p,*t]] if leaf(t) else flat(t[0],p+'0')+flat(t[1],p+'1')
def subtrees(t): return {t} if leaf(t) else {t}|subtrees(t[0])|subtrees(t[1])
def rewrite(t,old,new,p=''):
    if t==old: return new,[p]
    if leaf(t): return t,[]
    l,x=rewrite(t[0],old,new,p+'0'); r,y=rewrite(t[1],old,new,p+'1')
    return (l,r),x+y
def cfg(rows):
    ix={p:i for i,(p,_,_) in enumerate(rows)}
    def enter(p):
        while p not in ix: p+='0'
        return ix[p]
    def after(p):
        p=p.rstrip('1'); return enter(p[:-1]+'1') if p else 0
    def escape(p,side,n):
        for j in range(len(p)-1,-1,-1):
            if p[j]==side:
                n-=1
                if n==0: return after(p[:j]) if side=='0' else enter(p[:j])
        return 0
    return [([] if op=='CH' else [after(p)] if op=='CI' else
             [escape(p,'0',1),after(p)] if op=='CD' else
             [escape(p,'0' if op=='CB' else '1',n)]) for p,op,n in rows]
def metrics(t):
    r=flat(t); ns=subtrees(t)
    return {'dag':len(ns),'interior':sum(not leaf(x) for x in ns),
            'leaves':len(r),'guards':sum(2 if op=='CD' else 1 for _,op,_ in r),
            'depth':max(len(p) for p,_,_ in r),
            'right_CD':sum(op=='CD' and p.endswith('1') for p,op,_ in r)}
D5=('CD',5);D6=('CD',6);I1=('CI',1);I5=('CI',5);I6=('CI',6)
P=(D6,('CC',2));U=(P,('CB',1));V=(P,D6)
A=(D5,U);L=(A,D6);Z=(D5,('CC',1));R=(Z,U);E=(L,R)
rot=(((I1,I1),(I1,I1)),('CC',2));rot2=((I1,I1),((I1,I1),('CC',3)))
sharedA=(D5,(P,I6));shared=(sharedA,(D6,(sharedA,U)))
macros={'shared_cancellation':shared,'direct_equality_09':(L,((D5,(I6,('CC',2))),U)),
        'direct_equality_13':((A,(I5,A)),R)}
basepath=src/'replay/latest219_baseline/candidate-k219/sites219.json'
baseline=tree(json.loads(basepath.read_text())); report=[]
for name,macro in macros.items():
    file=src/'replay/research218_source'/f'{name}_sites.json'
    original=json.loads(file.read_text()); t=tree(original)
    rebuilt,roots=rewrite(baseline,E,macro); assert len(roots)==4 and rebuilt==t
    updated,macro_paths=rewrite(macro,U,V)
    eqonly,eqroots=rewrite(baseline,E,updated); assert eqroots==roots
    global_t,global_paths=rewrite(t,U,V)
    variants={'equality_only':(eqonly,[p+q for p in roots for q in macro_paths]),
              'whole_source':(global_t,global_paths)}
    row={'name':name,'source':desc(file),'before':metrics(t),'variants':{}}
    for mode,(new,paths) in variants.items():
        rr=flat(new); oldg=cfg(original); newg=cfg(rr)
        assert len(rr)==len(original)
        changed=[i for i,(x,y) in enumerate(zip(original,rr)) if x!=y]
        assert len(changed)==len(paths)
        assert [rr[i][0] for i in changed]==[p+'1' for p in paths]
        for i in range(len(rr)):
            if i in changed:
                assert original[i][1:]==['CB',1] and rr[i][1:]==['CD',6]
                assert oldg[i]==newg[i][:1]
            else: assert oldg[i]==newg[i]
        rotated,nrot=rewrite(new,rot,rot2); assert len(nrot)==81
        rotated_rows=flat(rotated); assert cfg(rr)==cfg(rotated_rows)
        dst=out/f'{name}-{mode}.sites.json'; dst.write_text(json.dumps(rr,separators=(',',':'))+'\n')
        rd=out/f'{name}-{mode}-retagged.sites.json';rd.write_text(json.dumps(rotated_rows,separators=(',',':'))+'\n')
        row['variants'][mode]={'metrics':metrics(new),'replacements':len(paths),'changed_ordinals':changed,
            'complete_CFG_checked':True,'output':desc(dst),'retagged_metrics':metrics(rotated),
            'retagged_CFG_equal':True,'retagged_output':desc(rd),'retagged_rotations':len(nrot)}
    report.append(row)
result={'status':'EXACT_U_REWRITE_SOURCE_CENSUS_PASS','reader':desc(Path(__file__)),
        'baseline':desc(basepath),'cases':report,'execution_scope':'Own literal reconstruction/rewrite/CFG only. No delivered execution, compiler, table allocation, runtime or startup.',
        'proof_scope':'U=((D6,C2),B1) and V=((D6,C2),D6) have the same all-natural open contract. Existing equality proofs and contextual replacement supply source semantics, not finite diagnostics.',
        'limits':'No physical state saving, full binary correctness or <=218 result inferred from source DAG counts.'}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps([{ 'name':x['name'],'before':x['before'],'variants':{k:{q:v[q] for q in ['metrics','replacements','retagged_metrics']} for k,v in x['variants'].items()}} for x in report],indent=2))
