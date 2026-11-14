#!/usr/bin/env python3
"""Joint association and independent axiom-head parameter/order experiment.

Extends the archived fixed-word annealer with axiom-schema parameter
permutations, antecedent exchanges and head order changes. Does not use RePair.
"""
from pathlib import Path
import argparse,itertools,json,sys,time,random,math,collections
from direct_head_permutations import s,v,SEARCH,BASE,ATOMS,HEAD_LENGTHS,PREFIX_LEN,leaves
PERMS=list(itertools.permutations('DHA'))
TOKEN={'node49':'P','node58':'H','node55':'D','node70':'A','node65':'C','node72':'r','node75':'s','node142':'g','node150':'j',s.INC:'i',s.BREAK:'z'}
REV={b:a for a,b in TOKEN.items()}
HEAD_END=PREFIX_LEN+sum(HEAD_LENGTHS)

def reword(t,word):
 i=0
 def rec(t):
  nonlocal i
  if s.c.isnode(t):return rec(t[0]),rec(t[1])
  r=REV[word[i]];i+=1;return r
 nt=rec(t);assert i==len(word);return nt

def emitted(meta,tail):
 heads,_=v.formulas(meta['bits'])
 heads=[v.rename(h,dict(zip('DHA',PERMS[k]))) for h,k in zip(heads,meta['perms'])]
 return v.PREFIX+''.join(v.emit(heads[i]) for i in meta['order'])+tail

def clone(meta):return {'bits':meta['bits'],'perms':meta['perms'][:],'order':meta['order'][:]}
def identity():return {'bits':0,'perms':[0]*6,'order':list(range(6))}

def score(t,exact_at=62):
 h,l,m,mi,_=s.attrs(t);pen=3*s.bad(t)+3*max(0,m-6)+3*max(0,mi-5)+max(0,h-38)
 rows,_,shape=s.c.build(t);ops=s.c.opportunities_fast(rows,shape)
 bound=len(shape)-len(s.c.max_matching(ops));folds=None
 if bound<=exact_at and pen==0:
  folds=s.bestcompatible_all(rows,shape);bound=len(shape)-len(folds)
 return bound+pen,pen,len(shape),folds

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--cycles',type=int,default=60);ap.add_argument('--steps',type=int,default=2000);ap.add_argument('--seed',type=int,default=2026111341);ap.add_argument('--force-single-head',action='store_true')
 ap.add_argument('--out',default=str(BASE/'head_association_search'));args=ap.parse_args();out=Path(args.out);out.mkdir(exist_ok=True)
 rng=random.Random(args.seed);pool=[];seen=set();wordtails={}
 for family in ('verified196','separate196'):
  t=s.c.read_grammar(SEARCH/(family+'.grammar.json'));word=''.join(TOKEN[x] for x in leaves(t));wordtails[family]=word[HEAD_END:]
  pool.append((t,identity(),family));seen.add(t)
 for path in sorted((SEARCH/'ties').glob('*.grammar.json')):
  t=s.c.read_grammar(path);word=''.join(TOKEN[x] for x in leaves(t));family=next((f for f,tail in wordtails.items() if word==emitted(identity(),tail)),None)
  if family and t not in seen:pool.append((t,identity(),family));seen.add(t)
 started=time.monotonic();count=0;counts=collections.Counter();best=62;best_changed=10**9;fullchecks=[]
 print('SEEDS',len(pool),'seed',args.seed,flush=True)
 for cycle in range(args.cycles):
  t,meta,family=rng.choice(pool);meta=clone(meta)
  if args.force_single_head:
   cases=[(5,1),(4,1),(1,2),(1,5),(0,1),(0,5)]
   h,k=cases[cycle%len(cases)];meta=identity();meta['perms'][h]=k
   t=reword(t,emitted(meta,wordtails[family]))
  cost,pen,n,folds=score(t);choices=list(s.nodes(t))
  for j in range(args.steps):
   roll=rng.random();nm=clone(meta)
   if roll<.76 or args.force_single_head:
    x=rng.choice(choices);opts=list(s.rotations(x))
    if not opts:continue
    nt=s.repl(t,x,rng.choice(opts));kind='rotation'
   elif roll<.91:
    h=rng.randrange(6);nm['perms'][h]=rng.randrange(6);nt=reword(t,emitted(nm,wordtails[family]));kind='parameter'
   elif roll<.96:
    a,b=rng.sample(range(6),2);nm['order'][a],nm['order'][b]=nm['order'][b],nm['order'][a];nt=reword(t,emitted(nm,wordtails[family]));kind='order'
   else:
    nm['bits']^=1<<rng.randrange(3);nt=reword(t,emitted(nm,wordtails[family]));kind='antecedent'
   count+=1;counts[kind]+=1;nc,np,nn,nf=score(nt)
   changed=nm!=identity()
   if np==0 and changed and nc<best_changed:
    best_changed=nc;print('CHANGED BEST',nc,family,nm,'seconds',round(time.monotonic()-started,2),flush=True)
    (out/'best_changed.json').write_text(json.dumps({'family':family,'meta':nm,'cost':nc,'grammar':s.encode(nt)},indent=2)+'\n')
   temp=.08+.9*(1-j/args.steps)**2
   if nc<=cost or rng.random()<math.exp(min(0,(cost-nc)/temp)):
    t,meta,cost,pen,n,folds=nt,nm,nc,np,nn,nf;choices=list(s.nodes(t))
    if cost<=62 and pen==0 and t not in seen:
     seen.add(t)
     if len(pool)<400:pool.append((t,clone(meta),family))
     if changed:(out/('tie_'+str(len(seen))+'.json')).write_text(json.dumps({'family':family,'meta':meta,'cost':cost,'grammar':s.encode(t)},indent=2)+'\n')
    if cost<best:
     best=cost;print('NEW BEST',best,n,'changed',changed,'seconds',round(time.monotonic()-started,2),flush=True)
    if cost<=61 and pen==0:
     rows,_,shape=s.c.build(t);chosen=s.bestcompatible_all(rows,shape);folded,alias=s.apply(rows,chosen);sites,ins,contracts=s.c.source(t)
     result=s.c.validate(folded,contracts);data={'family':family,'meta':meta,'cost':cost,'folds':chosen,'grammar':s.encode(t),'runtime':result}
     fullchecks.append(data);(out/('candidate_'+str(len(fullchecks))+'.json')).write_text(json.dumps(data,indent=2)+'\n');print('FULL',result,flush=True)
     if result['ok']:
      (out/'candidate195.native.tm').write_text('#! start 74\n'+''.join(f'{q} {b} {w} {"R" if d else "L"} {nxt}\n'for(q,b),(w,d,nxt)in sorted(folded.items())))
      (out/'candidate195.word.txt').write_text(emitted(meta,wordtails[family])+'\n')
      print('RUNTIME SUCCESS; startup and arithmetic binding still required',flush=True);return
   if count%5000==0:s.attrs.cache_clear()
  receipt={'seed':args.seed,'force_single_head':args.force_single_head,'completed_cycles':cycle+1,'attempted_proposals':count,'counts':dict(counts),'pool_size':len(pool),'best_cost':best,'best_changed_cost':best_changed,'seconds':time.monotonic()-started,'runtime_candidates':len(fullchecks),'scope':'Joint fixed-association leaf substitution and shared-subtree rotation search; valid source transformations require unchanged prefix/gate plus six independent parameterized head schemas and recorded head order.'}
  (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('CYCLE',cycle+1,receipt,flush=True)

if __name__=='__main__':main()
