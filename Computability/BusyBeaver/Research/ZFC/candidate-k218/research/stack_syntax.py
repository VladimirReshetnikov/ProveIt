from pathlib import Path
import json,hashlib
P=Path('/tmp/zfc-intake188/drop-k218/extracted/K218_Construction_2026-10-20')
A=Path('/tmp/zfc-intake187/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20')
B=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k219')
O=Path(__file__).resolve().parent
cfg=json.loads((A/'machine/construction.json').read_text());old=json.loads((B/'sites219.json').read_text());new=json.loads((P/'machine/sites218.json').read_text())
def structure(rows):
 raw={}
 for p,o,a in rows:
  n=raw
  for b in p:n=n.setdefault(b,{})
  assert not n;n['v']=(o,a)
 intervals={};count=0;allnodes=set()
 def go(n,p=''):
  nonlocal count
  start=count
  if 'v'in n:t=n['v'];count+=1
  else:t=(go(n['0'],p+'0'),go(n['1'],p+'1'))
  intervals[p]=(start,count,t);allnodes.add(t);return t
 tree=go(raw);return tree,intervals,len(allnodes)
ot,oi,oc=structure(old);nt,ni,nc=structure(new)
reverse={(a,b):(p,t)for p,(a,b,t)in ni.items()}
trans=[];bad=[]
for p in cfg['retag_rotation_paths']:
 a,b,t=oi[p]
 q,u=reverse.get((a,b),(None,None))
 row={'old_prefix':p,'interval':[a,b],'new_prefix':q,'same_subtree':u==t}
 (trans if u==t else bad).append(row)
reports={'retag_intervals':trans,'retag_missing':bad,'zero_ordinals':cfg['zero_terminal_ordinals'],'states_scope':'Syntax-only count, no new runtime/startup result'}
assert not bad
for name in ('zero_terminal','retagged','composed'):
 rows=json.loads(json.dumps(new))
 if name in('retagged','composed'):
  paths=[r['new_prefix']for r in trans];assert all(not a.startswith(b)for a in paths for b in paths if a!=b)
  for i,row in enumerate(rows):
   p,o,k=row
   matches=[r for r in paths if p.startswith(r)]
   if matches:
    assert len(matches)==1;r=matches[0];s=p[len(r):];tag=next(t for t in('00','01','1')if s.startswith(t));p=r+{'00':'0','01':'10','1':'11'}[tag]+s[len(tag):]
   if i in cfg['retag_control_ordinals']:assert(o,k)==('CC',2);k=3
   rows[i]=[p,o,k]
 if name in('zero_terminal','composed'):
  for i in cfg['zero_terminal_ordinals']:assert rows[i][1:]==['CB',1];rows[i][1:]=['CD',6]
 t,iv,n=structure(rows);raw=(json.dumps(rows,separators=(',',':'))+'\n').encode();(O/(name+'-sites.json')).write_bytes(raw)
 reports[name]={'source_sha256':hashlib.sha256(raw).hexdigest(),'dag_nodes':n,'leaves':len(rows),'guards':sum(2 if o=='CD'else 1 for p,o,k in rows),'maximum_depth':max(len(p)for p,o,k in rows),'changed_addresses':sum(x[0]!=y[0]for x,y in zip(rows,new)),'changed_primitives':sum(x[1:]!=y[1:]for x,y in zip(rows,new))}
(O/'stack-syntax.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps({k:v for k,v in reports.items()if k!='retag_intervals'},indent=2))
