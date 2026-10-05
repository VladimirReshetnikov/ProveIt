"""Independent finite check of all BR category and union identities."""
from pathlib import Path
from itertools import product
import json
import reconstruct as r

def reduce_mask(U,a):
 if U==1:return a&6
 if U==3:return (1 if a&3 else 0)|(a&4)
 return 3 if a.bit_count()>=2 else a
checks=0
for U in [1,3,7]:
 for C in range(8):
  r.need(r.cnt((U,C))==r.cnt((U,reduce_mask(U,C))),'h category');checks+=1
 for C,D in product(range(8),repeat=2):
  c,d=reduce_mask(U,C),reduce_mask(U,D)
  r.need(r.cnt((U,C,D))==r.cnt((U,c,d)),'chi category');checks+=1
  r.need(r.cnt((U,C|D))==r.cnt((U,c|d)),'pair union category');checks+=1
 for columns in product(range(8),repeat=3):
  images=tuple(reduce_mask(U,a) for a in columns)
  for mask in range(1,8):
   a=b=0
   for i in range(3):
    if mask&(1<<i):a|=columns[i];b|=images[i]
   r.need(r.cnt((U,a))==r.cnt((U,b)),'q_BR union profile');checks+=1
out={'all_pass':True,'category_and_union_equalities':checks,'generic_columns_remain_distinct':r.cnt((7,3,3))==1}
r.need(out['generic_columns_remain_distinct'],'generic-column distinction')
Path(__file__).with_name('category_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
