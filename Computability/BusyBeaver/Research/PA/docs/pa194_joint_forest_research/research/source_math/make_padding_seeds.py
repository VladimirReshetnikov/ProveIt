from make_dup_seeds import *
import random
seeds=[];info=[]
for shapeid,s in enumerate(shapes):
 base=word(s)
 for b in bounds+[189]:
  for n in range(1,6):
   w=base[:b]+['node49']*n+base[b:]
   seeds.append(adapt(s,w));info.append(dict(shape=shapeid,insertion=b,copies=n,tokens=len(w),kind='truth padding'))
 rng=random.Random(347)
 for j in range(250):
  bs=rng.sample(bounds,rng.randint(2,5));w=[]
  for k,x in enumerate(base):
   if k in bs:w+=['node49']
   w.append(x)
  seeds.append(adapt(s,w));info.append(dict(shape=shapeid,positions=bs,tokens=len(w),kind='truth padding'))
tokens=(PRIMARY/'research/joint_grammar/joint_ax11/seeds_h.txt').read_text().splitlines();nb=int(tokens[0]);text=tokens[:1+nb]+[str(len(seeds))]
for tid,t in enumerate(seeds):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}')
 text.extend(' '.join(map(str,row))for row in ns)
(HERE/'padding.templates.txt').write_text('\n'.join(text)+'\n');(HERE/'padding.seeds.json').write_text(json.dumps(info,indent=2)+'\n')
print('Padding seeds',len(seeds))
