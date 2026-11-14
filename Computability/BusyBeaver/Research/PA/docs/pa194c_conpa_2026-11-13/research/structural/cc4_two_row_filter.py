from pathlib import Path
import sys,json,time,collections
PACKAGE=Path(__file__).resolve().parents[2]
ROOT=PACKAGE/'reference/pa194';OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'));import compiler as c
base=c.raw_nodes();ax=c.read_grammar(ROOT/'construction/source/pa194.grammar.json');oldsites,oldins,oldcs=c.source(ax)
nodes=dict(base);nodes['node170']=('node28',('node35','node169'));nodes['node166']=(base['node166'][0],('leaf','continueTo',4));c.raw_nodes=lambda:nodes
sites,ins,cs=c.source(ax);assert ins==oldins
rows={}
for line in (ROOT/'construction/tables/pa194.native.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
rows.update({(214,0):(0,True,95),(214,1):(1,True,188),(188,0):(0,True,111),(188,1):(1,True,312)})
coverage=collections.defaultdict(set);failed=[]
for i,con in enumerate(cs):
 def observe(s):
  q,onl,l,r=s;bit=c.headbit(l if onl else r)
  if bit in (0,1):coverage[q,bit].add(i)
 if c.run(rows,con,observe=observe) is None:failed.append(i)
print('BASE_FAILS',[(cs[i][0],cs[i][1])for i in failed],flush=True)
assert all(cs[i][0]==3660 for i in failed)
candidates=json.loads((OUT/'cc4_two_row_candidates.json').read_text());tested=0;skipped=0;valid=[];results=[]
for cand in candidates:
 q,b,w,d,n=cand['patch']
 if q in c.BOXSTATES:skipped+=1;continue
 trial=dict(rows);trial[18,1]=tuple([cand['first'][0],cand['first'][1]==1,cand['first'][2]]);trial[q,b]=w,d==1,n
 affected=coverage[q,b]|coverage[18,1]|set(failed)
 tested+=1;out=None
 for i in sorted(affected,key=lambda i:(cs[i][0]!=3660,i)):
  if c.run(trial,cs[i],fuel=2500) is None:out=cs[i][0],cs[i][1];break
 if out is None:
  full=c.validate(trial,cs);print('SURVIVOR',cand,full,flush=True)
  if full['ok']:valid.append(cand)
 results.append({'candidate':cand,'first_failure':out,'affected':len(affected)})
print('DONE tested',tested,'excluded_box_edits',skipped,'valid',len(valid),flush=True)
(OUT/'cc4_two_row_filter.json').write_text(json.dumps({'source_equal':True,'tested':tested,'excluded_box_edits':skipped,'valid':valid,'failures':results},indent=2)+'\n')
