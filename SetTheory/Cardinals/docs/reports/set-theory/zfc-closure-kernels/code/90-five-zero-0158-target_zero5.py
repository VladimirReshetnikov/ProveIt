"""Coordinate the remaining source bottlenecks in a relaxed50 grammar."""
import json,sys
from pathlib import Path
source=Path(sys.argv[1]);sys.argv=[sys.argv[0],str(source),'5']
# The shared evaluator also validates exact folded-route projections and locks.
exec((Path(__file__).resolve().parent/'repair_zero_strong.py').read_text().split('current={')[0])
g={w:(a,b)for w,a,b in d['rules']};routes=d['routes']
def setrule(w,a,b):
 w,a,b=map(canon,(w,a,b));assert w==a+b and permitted(a,b)
 assert w not in term
 g[w]=(a,b)
setrule('eijkKCeijkbI','eijk','KCeijkbI')
setrule('KCeijkbI','KC','eijkbI')
setrule('VqkjGqkjGVqkjG','V','qkjGqkjGVqkjG')
setrule('qkjGqkjGVqkjG','qkjG','qkjGVqkjG')
setrule('eijkKCqkjGqkjGVqkjG','eijkKCqkjG','qkjGVqkjG')
for r in routes:
 if (r['source'],r['read'])==(183,1):r['word']=canon('eijkKCqkjGqkjGVqkjG')
answer=close(g,routes);assert answer is not None
g,routes=answer
print('coordinated',len(g),props(g))
# Decrease the source AX root leading depth by rotating its left spine.
ax=byast[205]
for step in range(4):
 # Its parent's additional zero permits leading depth only4 here.
 if props(g)[3]==0:break
 a,b=g[ax]
 if a not in g:break
 x,y=g[a];part=y+b
 if not permitted(x,part)or(part not in g and part not in term and not permitted(y,b)):break
 h=dict(g)
 if part not in h and part not in term:h[part]=(y,b)
 h[ax]=(x,part);answer=close(h,routes)
 if answer is None:break
 h,rr=answer
 if props(h)[3]>props(g)[3]:break
 g,routes=h,rr
 print('AX rotation',step,len(g),props(g))
d.update(rules_count=len(g),rules=[[w,*ab]for w,ab in sorted(g.items())],routes=routes,properties=list(props(g)),status='TARGETED_ZERO5_COORDINATED_REPAIR')
out=source.with_name(source.stem+'-targeted.json');out.write_text(json.dumps(d,indent=2)+'\n');print(out)
