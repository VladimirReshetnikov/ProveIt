import sys as _assertion_sys
if not __debug__ or _assertion_sys.flags.optimize:
    raise RuntimeError("Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.")
"""Bounded exact search over legal local sequence parenthesizations."""
from shifted_source import *

def shapes(items):
    if len(items)==1:return [items[0]]
    return [node(a,b)for k in range(1,len(items))for a in shapes(items[:k])for b in shapes(items[k:])]
def position(t,x,p=''):
    if t==x:return p
    if t[0]=='N':return position(t[1],x,p+'0')or position(t[2],x,p+'1')
    return None

def pair_variants():
    out=[]
    for i,dt in enumerate(shapes([I(Y),I(Y),('c','dt')])):
      dt=resolve(node(Dn(T),dt),'dt')
      for j,dy in enumerate(shapes([I(T),I(T),('c','dy')])):
        dy=resolve(node(Dn(Y),dy),'dy')
        for k,body in enumerate(shapes([dy,transfer(T,Y),I(Y),('c','outer')])):
            out.append(((i,j,k),node(dt,resolve(node(Dn(X),body),'outer'))))
    return out

def unpair_variants(s):
    out=[]
    even=resolve(node(node(Dn(s),('b','test')),('b','outer')),'test')
    for i,half in enumerate(shapes([even,('guard',s),I(Y),('c','half')])):
      p=position(half,('guard',s))
      if p.count('0')!=1:continue
      def restore(t):
        if t==('guard',s):return Dn(s)
        return node(restore(t[1]),restore(t[2]))if t[0]=='N'else t
      half=resolve(restore(half),'half')
      for j,outer in enumerate(shapes([half,I(X),transfer(Y,s),('c','outer')])):
        out.append(((i,j),resolve(outer,'outer')))
    return out

def nodeset(t):
    if t[0]!='N':return set()
    return {t}|nodeset(t[1])|nodeset(t[2])

def main():
    pv=pair_variants();lv=unpair_variants(L);wv=dict(unpair_variants(W));best=None;rows=[]
    for pk,pair in pv:
      for uk,upL in lv:
        upW=wv[uk]
        root,_=expand({115:upL,116:upW,162:pair});stats=sizes(root)
        row={'pair_shape':pk,'unpair_shape':uk,'whole_nodes':stats['hashcons_binary_nodes'],'depth':stats['max_depth'],'zero_run':stats['max_zero_run']}
        rows.append(row)
        score=(row['whole_nodes'],row['zero_run'],row['depth'])
        if best is None or score<best[0]:best=(score,row,pair,upL,upW,root)
    score,row,pair,upL,upW,root=best
    for a in range(8):
      for b in range(10):
        v=[0]*9;v[X]=a;v[T]=b;r,st=run(pair,v);assert r==('ok',)and v[Y]==(1<<a)*(2*b+1)-1 and v[X]==v[T]==0
    for s,t in[(L,upL),(W,upW)]:
      for n in range(1025):
        v=[0]*9;v[s]=n;r,st=run(t,v);assert r==('ok',)and v[s]==0 and (1<<v[X])*(2*v[Y]+1)-1==n
    result={'pair_variants':len(pv),'matched_unpair_variants':len(lv),'combinations':len(rows),'best':row,'baseline_nodes':219,'new_source':sizes(root),
            'cost_distribution':dict(collections.Counter(r['whole_nodes']for r in rows)),'all_rows':rows}
    (OUT/'shape-search-results.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'best-shifted-source.json').write_text(json.dumps(serialize(root),indent=2)+'\n')
    (OUT/'best-helpers.json').write_text(json.dumps({k:serialize(v)for k,v in {'pair':pair,'unpairL':upL,'unpairW':upW}.items()},indent=2)+'\n')
    audit=entry_contract_abstraction({115:upL,116:upW,162:pair})
    assert audit['unpair_scratch_clean'] and audit['pair_output_clean']
    (OUT/'best-clean-entry-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    oldset=nodeset(expand()[0]);newset=nodeset(root)
    detail={'old_total':len(oldset),'new_total':len(newset),'exact_unchanged_nodes':len(oldset&newset),
            'old_only':len(oldset-newset),'new_only':len(newset-oldset),
            'helper_sizes':{k:sizes(v)for k,v in {'pair':pair,'unpairL':upL,'unpairW':upW}.items()},
            'best_clean_audit':{k:v for k,v in audit.items()if k!='entry_masks'}}
    dirty=0
    for x in range(4):
      for y in range(4):
        for n in range(20):
          vals=[0]*9;vals[X]=x;vals[Y]=y;vals[L]=n
          target=(1<<x)*(2*y+1+n)-1
          ret,_=run(upL,vals)
          assert ret==('ok',)and vals[L]==0 and (1<<vals[X])*(2*vals[Y]+1)-1==target
          dirty+=1
    for x in range(5):
      for y in range(5):
        for t in range(6):
          vals=[0]*9;vals[X]=x;vals[Y]=y;vals[T]=t
          target=(1<<x)*(2*t+1+y)-1
          ret,_=run(pair,vals)
          assert ret==('ok',)and vals[X]==vals[T]==0 and vals[Y]==target
          dirty+=1
    detail['dirty_contract_tests']=dirty
    (OUT/'best-cost-details.json').write_text(json.dumps(detail,indent=2)+'\n')
    print({k:v for k,v in result.items()if k not in('all_rows','new_source')})
if __name__=='__main__':main()
