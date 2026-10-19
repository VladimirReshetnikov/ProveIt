"""Compile transformed source DAG while retaining independently identified binary roles."""
from pathlib import Path
import re,json,collections,functools,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE=ROOT/'vendor/context246'
raw=(BASE/'sources/Prog254.v').read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
pat=r'(CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
ns=[tuple(tuple([v[0],int(v[1])] if len(v)==2 else [v[0],None]) for v in [a.split(),b.split()]) for a,b in re.findall(r'\('+pat+r',\s*'+pat+r'\)',raw)]
assert len(ns)==6459
T={}
for s in (BASE/'machine/zfc_prefix246_old.tm').read_text().splitlines():
 if not s or s.startswith('#'):continue
 q,b,w,d,t=s.split();T[int(q),int(b)]=(int(w),d,int(t))
qocc={int(q):nn for q,nn in json.loads((ROOT/'experiments/logic/inputs/first_decoder_state_map.json').read_text()).items()}
nq={n:q for q,nn in qocc.items() for n in nn}
assert len(nq)==6459
entries=[];intern={}
def mk(v):
 if v not in intern:intern[v]=len(entries);entries.append(v)
 return intern[v]
@functools.cache
def old(n):
 return mk(('N',*(old(e[1]) if e[0]=='CN' else mk(e) for e in ns[n])))
oldroot=old(0)
oldsigs=set(old(n) for n in range(6459));sigq=collections.defaultdict(set);qsig=collections.defaultdict(set)
for n,q in nq.items():sigq[old(n)].add(q);qsig[q].add(old(n))
term=collections.defaultdict(collections.Counter)
for n,q in nq.items():
 for b,e in enumerate(ns[n]):
  if e[0]!='CN':term[e+(b,)][T[q,b]]+=1

def newgraph(path):
 data=json.loads(Path(path).read_text());es=data['entries'];memo={}
 def rec(n):
  if n in memo:return memo[n]
  e=es[str(n)];v=('N',rec(e[1]),rec(e[2])) if e[0]=='N' else tuple(e)
  memo[n]=mk(v);return memo[n]
 root=rec(data['root']);return root,set(memo.values()),data

def reachable(root):
 out=set()
 def walk(n):
  if n in out:return
  out.add(n)
  if entries[n][0]=='N':walk(entries[n][1]);walk(entries[n][2])
 walk(root);return out

def report(path):
 root,allnew,data=newgraph(path);newpairs={s for s in allnew if entries[s][0]=='N'}
 print('oldpairs',len(oldsigs),'source states',len(qsig),'newpairs',len(newpairs),'retained',len(newpairs&oldsigs),'new',len(newpairs-oldsigs))
 for q,ss in sorted(qsig.items()):
  if len(ss)>1:print('ALIAS',q,[(s,entries[s],s in newpairs) for s in sorted(ss)])
 print('TERMS')
 for k,c in sorted(term.items(),key=str):print(k,dict(c))
 print('POSSIBLE FROZEN ROLES')
 for q,ss in sorted(qsig.items()):
  if not ss&newpairs:continue
  for b in (0,1):
   w,d,t=T[q,b]
   if d=='L' and all(entries[entries[s][b+1]][0]=='N' for s in ss&newpairs):print(q,b,T[q,b],[(s,entries[s]) for s in sorted(ss&newpairs)])
 return root,newpairs
if __name__=='__main__':report(sys.argv[1])

def compile_hints(graphpath,hintpath,output):
 data=json.loads(Path(graphpath).read_text());E={int(k):v for k,v in data['entries'].items()}
 hints=json.loads(Path(hintpath).read_text())['entries'];roles={};qs=collections.defaultdict(list);none=[]
 for e in hints:
  choices=e['original_structural_states'] or [q for q,n in e['same_interval_old_states']]
  assert len(choices)<=1
  if choices:roles[e['grammar_node']]=choices[0];qs[choices[0]].append(e['grammar_node'])
  else:none.append(e['grammar_node'])
 free=sorted(set(qocc)-set(qs))
 if len(free)<len(none):free+=list(range(256,256+len(none)-len(free)))
 else:free=free[:len(none)]
 for s,q in zip(none,free):roles[s]=q;qs[q].append(s)
 R=T.copy();conflicts=[];direct={}
 for q,sigs in qs.items():
  for b in (0,1):
   wants=[]
   for s in sigs:
    child=E[E[s][b+1]]
    if child[0]=='N':row=(b,'R',roles[E[s][b+1]])
    else:
     oldsig=qsig.get(q,set())
     options={T[q,b] for ss in oldsig if entries[entries[ss][b+1]]==tuple(child)}
     if len(options)==1:row=next(iter(options))
     else:
      opts=term[tuple(child)+(b,)];assert opts,(q,s,b,child)
      row=opts.most_common(1)[0][0]
    wants.append(row)
   if len(set(wants))==1:R[q,b]=wants[0];direct[q,b]=wants[0]
   else:conflicts.append((q,b,list(zip(sigs,wants))))
 (HERE/(output+'_roles.json')).write_text(json.dumps({'roles':roles,'conflicts':conflicts,'free_assignment':list(zip(none,free))},indent=2)+'\n')
 save_table(R,HERE/(output+'.tm'))
 print('COMPILED rawstates',len({q for q,b in R}),'conflicts',conflicts)
 return R,roles,conflicts,E,hints,direct

def save_table(R,path):
 Path(path).write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(R.items())))
