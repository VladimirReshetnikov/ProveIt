import words,itertools,json
from pathlib import Path
symbols=list(dict.fromkeys(words.w));ids={s:i for i,s in enumerate(symbols)}
perms=list(itertools.permutations('DHA'))
mids=[ids[words.TOK[c]] for c in 'DHA']
H=[]
for flip in [False,True]:
 hh=[]
 for j in range(6):
  variants=[]
  for flags in range(8):
   h=words.emit(words.heads(flags,flip)[j])
   for p in perms:
    remap=dict(zip(mids,[ids[words.TOK[c]] for c in p]))
    seq=[remap.get(ids[t],ids[t]) for t in h]
    if seq not in variants:variants.append(seq)
  hh.append(variants)
 H.append(hh)
G=[[[ids[t] for t in words.emit(words.gate(swap,flip))]for swap in [False,True]]for flip in [False,True]]
obj={'symbols':symbols,'prefix':[ids[t] for t in words.prefix],'suffix':[ids[t]for t in words.suffix],'heads':H,'gate':G}
Path('config.json').write_text(json.dumps(obj,indent=2))
def cpp(x):return '{'+','.join(cpp(a)if isinstance(a,list)else str(a)for a in x)+'}'
Path('config.hpp').write_text('\n'.join(['std::vector<int> prefix='+cpp(obj['prefix'])+';','std::vector<int> suffix='+cpp(obj['suffix'])+';','std::vector<std::vector<std::vector<std::vector<int>>>> heads='+cpp(H)+';','std::vector<std::vector<std::vector<int>>> gate='+cpp(G)+';','const int NT='+str(len(symbols))+';']))
print('head options',[[len(a)for a in f]for f in H],symbols)
