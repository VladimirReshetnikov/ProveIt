#!/usr/bin/env python3
"""Replay frozen finite compiler-price screens. These are not TM correctness certificates."""
from pathlib import Path
import gzip,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import compiler as c

def read_table(path):
 rows={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R')
  rows[q,b]=w,d=='R',n
 return rows

def tup(t):return tuple(map(tup,t))if isinstance(t,list)else t

def main():
 if not __debug__:raise RuntimeError('Run with assertions enabled.')
 raw={k:read_table(HERE/'reference'/f)for k,f in [('4','raw.native.tm'),('7','radix7_rawbase.tm')]}
 inc=('leaf','inc',1)
 c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
 c.MACROS.update({'node69':179,'node54':114,'inc3':330})
 with gzip.open(HERE/'inputs/finite_cases.json.gz','rt')as f:cases=json.load(f)
 summary={}
 for case in cases:
  c.machine=lambda:(raw[case['raw_family']],[])
  rows,idx,shape=c.build(tup(case['grammar']))
  ops=c.opportunities_fast(rows,shape);folds=c.max_matching(ops)
  actual={'name':case['name'],'raw':len(rows)//2,'readers':len(shape),'max_disjoint_folds':len(folds),'optimistic':len(rows)//2-len(folds)}
  assert actual==case['expected'],(case['name'],actual,case['expected'])
  fam=summary.setdefault(case['family'],{'cases':0,'minimum_optimistic_states':999})
  fam['cases']+=1;fam['minimum_optimistic_states']=min(fam['minimum_optimistic_states'],actual['optimistic'])
 expected=json.loads((HERE/'finite_summary.json').read_text())
 assert summary==expected,(summary,expected)
 print(json.dumps({'status':'PASS','cases':len(cases),'summary':summary,'scope':'Finite grammar prices; no command completeness, simultaneous-fold realization, source runtime, or blank-start theorem is asserted.'},indent=2))
if __name__=='__main__':main()
