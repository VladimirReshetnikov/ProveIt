from pathlib import Path
import sys,json,itertools,collections
sys.path.insert(0,str(Path(__file__).parent/'vendor'))
import compiler as c, support as s
ROOT=Path(__file__).parent
baseline=s.read_table(ROOT/'data/primary201.native.tm')
qbase=s.read_table(ROOT/'data/q201.native.tm')
OUTPUT=ROOT/'replay/combinations'
OUTPUT.mkdir(parents=True,exist_ok=True)

def ops_checked(raw):
 incoming=collections.defaultdict(set)
 for (q,b),(w,d,n) in raw.items():incoming[n].add((w,d))
 return [(a,b,o) for a,b,o in c.opportunities_fast(raw,set(q for q,b in raw))
         if a!=74 and incoming[a]=={(0,True)} and incoming[b]=={(1,True)}]

def compatible(raw,ops):
 best=[]
 def rec(i,sel,used):
  nonlocal best
  if len(sel)+len(ops)-i<=len(best):return
  if i==len(ops):
   try:
    child,aliases=s.apply_folds(raw,sel)
    local=s.check_local_folds(raw,child,aliases,sel)
   except (AssertionError,KeyError):return
   best=sel.copy();return
  a,b,o=ops[i]
  if a not in used and b not in used:
   for acts in itertools.product(*o):rec(i+1,sel+[[a,b,acts]],used|{a,b})
  rec(i+1,sel,used)
 rec(0,[],set())
 return best

summary=[]
for qmode,k,mode,close in itertools.product([False,True],[4,5,6,8],['orig','cached','sums','cached_sums'],[False,True]):
 raw=dict(qbase if qmode else baseline)
 for key,v in baseline.items():
  if key[0]<1300:raw[key]=v
 if mode.startswith('cached'):
  for key,v in qbase.items():
   if key[0]<1300:raw[key]=v
 if mode=='sums':
  raw[38,1]=(1,True,30)
 if mode=='cached_sums':raw[214,1]=(1,True,30)
 if 'sums' in mode:
  raw.update({(310,1):(1,True,330),(330,0):(0,True,63),(330,1):(1,False,73)})
 if k in (5,6):
  raw.update({(190,0):(0,True,331),(190,1):(1,True,99 if k==5 else 331),
              (331,0):(0,True,61),(331,1):(1,True,99)})
 if k==8:raw.update({(190,0):(0,True,331),(190,1):(1,True,331),(331,0):(0,True,99),(331,1):(1,True,99)})
 if close:
  # Last emitter breakTo 1 has only one occurrence in these raw grammars.
  end=[key for key,v in raw.items() if key[0]>=2000 and key[1]==1 and v==(0,False,302)]
  assert len(end)==1,end
  raw[end[0]]=(1,True,21)
 ops=ops_checked(raw);folds=compatible(raw,ops);count=len(raw)//2-len(folds)
 name=f'{"Q" if qmode else "P"}_{mode}_{k}_{"Z" if close else "B"}'
 info=dict(name=name,working=count,unfolded=len(raw)//2,opportunities=len(ops),folds=folds)
 summary.append(info);print(json.dumps(info),flush=True)
 if count<=194 and (qmode or k!=4):
  child,_=s.apply_folds(raw,folds)
  (OUTPUT/(name+'.native.tm')).write_text(s.table_text(child))
  (OUTPUT/(name+'.folds.json')).write_text(json.dumps(folds))
  (OUTPUT/(name+'.raw.tm')).write_text(s.table_text(raw))
(OUTPUT/'combinations.json').write_text(json.dumps(summary,indent=2))
