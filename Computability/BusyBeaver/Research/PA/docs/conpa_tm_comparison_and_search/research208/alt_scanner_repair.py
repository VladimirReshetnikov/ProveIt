"""Explore extending the scanner without an added working state."""
from pathlib import Path
import sys,json,time,itertools
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'research_ipra/newsearch'))
import rotation_search as r
BASE=ROOT.parent/'support/alternative196'
m={(int(q),int(b)):(int(w),d=='R',int(t))for line in(BASE/'alternative196.native.tm').read_text().splitlines()for q,b,w,d,t in[line.split()]}
ll={tuple(p):('leaf',o,a)for p,o,a in json.loads((BASE/'sites.json').read_text())}
def tree(p=()):return ll[p]if p in ll else(tree(p+(0,)),tree(p+(1,)))
t=tree();c=next(c for c in r.cands(m,t) if c[:3]==(2065,2066,1));m,t=r.rotate(m,t,c)
dd=r.duplicates(m);m=r.merge(m,dd);ss,cs=r.contract_list(t)
dest=ROOT/'alt_first_rotation195.json'
dest.write_text(json.dumps({'rows':[[q,b,*v]for(q,b),v in sorted(m.items())],'sites':ss,'rotations':[c[:3]],'duplicates':dd},indent=2)+'\n')
helper=ROOT.parent/'search_root/repair_history_alt.py'
ns={'__file__':str(helper.resolve())}
code=helper.read_text().split('start=time.time();fail=[]')[0].replace('research208/alt_repair195_2.json',str(dest))
exec(code,ns);cs=ns['contracts'];baseline=ns['rows']
def run(c):
    try:return ns['ideal_run'](c)
    except (KeyError,ValueError,IndexError):return None
fails=[i for i,c in enumerate(cs)if run(c)is None]
print('ideal shared-router, old-scanner failures',len(fails),[cs[i][:2]for i in fails[:50]],flush=True)
hits=[];start=time.time()
for w,d,q in itertools.product((0,1),(False,True),sorted({q for q,b in baseline})):
    ns['rows']={**baseline,(34,0):(w,d,q)}
    if all(run(cs[i]) is not None for i in fails):
        bad=[i for i,c in enumerate(cs)if run(c)is None]
        print('preliminary',(w,d,q),'allfailures',len(bad),[cs[i][:2]for i in bad[:8]],flush=True)
        if not bad:hits.append((w,d,q))
print('DONE',hits,'seconds',time.time()-start,flush=True)
(ROOT/'alt_scanner_repair.json').write_text(json.dumps({'baseline_failures':[cs[i][:2]for i in fails],'one_row_hits':hits},indent=2)+'\n')
