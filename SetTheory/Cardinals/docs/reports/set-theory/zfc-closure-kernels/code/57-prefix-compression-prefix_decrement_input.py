#!/usr/bin/env python3
"""Conditional affine verification for the prefix-right decrement summary.

The new positive box contract returns the original exit state, with one 1
prepended to the left zipper, and decrements the selected register without
appending a spare. Its unbounded tape proof is a separate obligation.
"""
from pathlib import Path
from collections import defaultdict
from types import SimpleNamespace
import sys,json,argparse
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source/Computability/BusyBeaver/Research/ZFC'))
import candidate252_independent_audit as audit
source=ROOT/'source/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
sys.modules['cost_search']=SimpleNamespace()
raw=source.read_text().replace('40-len(pc)','43-len(pc)')
raw='''#!/usr/bin/env python3
"""Conditional affine executor with a prefix-right positive DEC contract.

The positive DEC oracle prepends one 1 to the left zipper and decrements the
selected primary register. It leaves the spare suffix unchanged. This changed
contract requires its own unbounded tape proof; the unchanged upstream positive
decrement box lemma does not establish it. Only the executor is included here:
the upstream audit/main entry points and their old support assertions are not.
"""
'''+raw[raw.index('from collections import Counter'):].split('\ndef audit(',1)[0]
old="""        if answer is not None:
            q,newstate=answer;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue"""
new="""        if answer is not None:
            if q=='43' and branch is not None and not branch[1] and seg[1][0]=='mark':
                context=canon_side(left,True)
                assert len(context)>=2 and context[0][0]==1 and context[0][2]>=1 and context[1][0]==0 and context[1][2]>=2,('prefix contract left-context premise',context)
                left=[('b',1)]+left
            q,newstate=answer;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue"""
assert old in raw
raw=raw.replace(old,new)
ns={'__name__':'strict_prefix_decrement'}
exec(compile(raw,str(source),'exec'),ns)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--permutation',default='0,2,6,8,7,5,3,1,4')
parser.add_argument('--out',default='compression/prefix_decrement_native')
args=parser.parse_args()
oldperm=(0,2,6,8,7,5,3,1,4);newperm=tuple(map(int,args.permutation.split(',')))
assert sorted(newperm)==list(range(9))
inverse={new:old for old,new in enumerate(oldperm)}
src=ROOT/'compression/mp_newperm_native';out=ROOT/args.out;out.mkdir(exist_ok=True)
(out/'strict_prefix_decrement.py').write_text(raw)
table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in audit.read_table((ROOT/'redesign/prefix_decrement252.tm').read_bytes()).items()}
for q,b in audit.SELECTOR_INCOMING:
 key=str(q),b;w,d,t=table[key]
 oldphysical=inverse[audit.SKIP.index(int(t))]
 table[key]=w,d,str(audit.SKIP[newperm[oldphysical]])
class Tracking(dict):
 def __init__(self,x):super().__init__(x);self.used=set()
 def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)
rows=[];usage=defaultdict(set)
for line in (src/'native_cases.txt').read_text().splitlines():
 fields=line.split();i=int(fields[0]);pc=fields[1];phys=int(fields[2]);zero=int(fields[3]);nxt=fields[4];overflow=int(fields[5]);effect=int(fields[6]);register=int(fields[7]);halt=int(fields[8])
 if phys>=0:phys=newperm[inverse[phys]];fields[2]=str(phys)
 if register>=0:register=newperm[inverse[register]];fields[7]=str(register)
 branch=(phys,bool(zero)) if phys>=0 else None
 eff=('inc' if effect==0 else 'dec',register) if effect>=0 else None
 target=[] if nxt=='-' else [('b',int(c)) for c in nxt]
 target += [('r',0,1,43+overflow+(effect==1)-(0 if nxt=='-' else len(nxt))),('b',1),('box',('plain',eff))]
 current=Tracking(table)
 try:rules,literal=ns['run'](current,pc,branch,ns['canon']([('b',1)],target),halt=bool(halt),fuel=1000)
 except Exception as error:
  print('FAILED CASE',i,fields);raise
 assert literal>0
 fields[-1]=str(sum(rules.values()));rows.append(' '.join(fields))
 for key in current.used:usage[key].add(i)
with (out/'native_table.txt').open('w') as f:
 for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])):f.write(f'{q} {b} {w} {d} {t}\n')
(out/'native_cases.txt').write_text('\n'.join(rows)+'\n')
with (out/'native_usage.txt').open('w') as f:
 for (q,b),indices in sorted(usage.items(),key=lambda x:(int(x[0][0]),x[0][1])):f.write(f'{q} {b} '+','.join(map(str,sorted(indices)))+'\n')
meta=json.loads((src/'metadata.json').read_text());meta.update(physical_permutation=list(newperm),logical_to_physical=[newperm[r]for r in audit.PHYS],minimum_gap=43,baseline_cases_checked=len(rows),positive_decrement='prefix shifts right by one; spare suffix unchanged',conditional_contract='left-zipper prepend 1 at positive DEC macro')
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
(out/'table.tm').write_bytes(audit.encode({(int(q),b):(w,d,int(t))for(q,b),(w,d,t)in table.items()}))
print('Prefix decrement inputs ready; all',len(rows),'conditional affine cases passed.')
