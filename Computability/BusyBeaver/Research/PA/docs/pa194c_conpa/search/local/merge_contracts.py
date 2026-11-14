"""Search whole universal instruction contracts after direct state quotients.

Both actions of the retained state are chosen independently from the two
old states. Arithmetic-box controls and the dispatcher are not merged.
Target renaming may change outward box edges; any positive preliminary
result additionally needs an independent physical/list-lemma replay.
This explores nonlocal rejoining at source-frame boundaries, not merely a
fixed-width local window. A candidate is recorded only after all contracts pass; final acceptance
also requires a full blank-frame startup and independent physical check.
"""
from pathlib import Path
import sys,time,json,itertools,argparse,os
HERE=Path(__file__).resolve().parent
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--family',default='S');args=ap.parse_args()
 if args.family=='C':
  sys.path.insert(0,os.environ.get('PA194C_CONSTRUCTION',str(HERE.parent.parent/'construction')))
  import build194C as a
  a.enable_combined();c=a.c
  rows=a.b.read_table(a.OUT/'pa194C.native.tm');sites,ins,cs=c.source(c.read_grammar(a.HERE/'source/pa194.grammar.json'))
  blank_steps=57922
 else:
  import symbolic_runtime as c
  rows=c.table();sites,ins,cs=c.source();blank_steps=58154
 started=time.monotonic();touches={q:set()for q,b in rows}
 for i,con in enumerate(cs):
  seen=set();v=c.run(rows,con,observe=lambda s:seen.add(s[0]));assert v is not None
  for q in seen:
   if q in touches:touches[q].add(i)
 forbidden=c.BOXSTATES|{74,84,254}
 eligible=sorted(set(touches)-forbidden)
 candidates=0;cases=0;hist={};successes=[]
 for a,b in itertools.combinations(eligible,2):
  # First test witnesses of each semantic role, then the complete affected set.
  # Testing hundreds of contracts that use only the unchanged role first would
  # waste most of the search time on an obviously incompatible other role.
  chosen=[]
  groups=[touches[b]-touches[a],touches[a]-touches[b],touches[a]&touches[b],touches[b],touches[a]]
  for group in groups:
   seq=sorted(group)
   if seq:
    for idx in sorted(set([0,len(seq)-1]+[j*len(seq)//8 for j in range(1,8)])):
     if seq[idx]not in chosen:chosen.append(seq[idx])
  interesting=chosen+sorted((touches[a]|touches[b])-set(chosen))
  if not interesting:continue
  base={(q,x):(w,d,b if n==a else n)for(q,x),(w,d,n)in rows.items()if q!=a}
  for s0,s1 in itertools.product((a,b),repeat=2):
   new=dict(base)
   for x,s in enumerate((s0,s1)):
    w,d,n=rows[s,x];new[b,x]=(w,d,b if n==a else n)
   candidates+=1;done=0
   for i in interesting:
    done+=1;cases+=1
    if c.run(new,cs[i]) is None:break
   else:
    print('CANDIDATE',a,b,s0,s1,'affected',len(interesting),flush=True)
    check=c.validate(new,cs);assert check['ok']
    rec={'remove':a,'keep':b,'row_sources':[s0,s1],'contracts':check}
    out=HERE/f'merge_{args.family}_{a}_{b}_{s0}_{s1}.tm'
    out.write_text(''.join(f'{q} {x} {w} {"R"if d else "L"} {n}\n'for(q,x),(w,d,n)in sorted(new.items())))
    rec['table']=str(out);successes.append(rec)
   hist[done]=hist.get(done,0)+1
  if candidates%1000==0:print('progress',candidates,'cases',cases,'elapsed',round(time.monotonic()-started,2),flush=True)
 receipt={'family':args.family,'candidate_tables':candidates,'contracts_executed':cases,'symbolic_step_bound':1024,'eligible_states':eligible,'successes':successes,'seconds':time.monotonic()-started,'histogram':hist}
 (HERE/f'merge_contracts_{args.family}.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:v for k,v in receipt.items()if k not in('eligible_states','histogram')},indent=2),flush=True)
if __name__=='__main__':main()
