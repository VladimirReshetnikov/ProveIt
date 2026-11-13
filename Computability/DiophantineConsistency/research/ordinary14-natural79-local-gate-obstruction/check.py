#!/usr/bin/env python3
"""Exact modular counterexamples to a finite class of local graph identities."""
from pathlib import Path
import gzip,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
g=json.loads(pin(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
t=pin(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36').decode()
rows=[]
for line in t.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0].splitlines():
 if not line.strip():continue
 m=re.fullmatch(r'\s*let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)\s*',line);assert m,line
 n,x,op,y=m.groups();parse=lambda z:int(z) if z.isdecimal() else z
 rows.append([n,op,parse(x),parse(y)])
assert rows==g['source'] and len(rows)==79 and g['output']=='out'
assert re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.var (\d+)',t)==[(v,str(i)) for i,v in enumerate(g['witnesses'])]
assert re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.constant \(p (\d+)\)',t)==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])]
assert [x.strip() for x in re.search(r'-- END LITERAL GRAPH\s*⟨([^⟩]+)⟩',t).group(1).split(',')][:6]==['F0','F1','Fa','Fs','guard','out']
# These are the externally recorded P72 bytes. Their identification with any
# Lean port expression or displayed PDF remains an independent obligation.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
mod=2**61-1;ports={};port_hashes={}
for name in g['fixed_numerals']:
 v=bind['ports'][name];assert b115['ports'][name]['sha256_raw']==v['sha256_raw'] and b115['ports'][name]['sha256_gzip']==v['sha256_gzip']
 z=pin(p72/v['path'],v['sha256_gzip']);raw=gzip.decompress(z)
 assert len(raw)==v['raw_bytes'] and sha(raw)==v['sha256_raw']
 ports[name]=int.from_bytes(raw,'little')%mod;port_hashes[name]=v['sha256_raw']
witness={n:i*i*7919+i*1234567+13579 for i,n in enumerate(g['witnesses'],1)}
assert all(x>=0 for x in witness.values())
values={n:v%mod for n,v in witness.items()};values.update(ports)
def val(x):return values[x] if isinstance(x,str) else x%mod
def op(a,o,b):
 assert o in ('+','-','*')
 return (a+b if o=='+' else a-b if o=='-' else a*b)%mod
for n,o,x,y in rows:values[n]=op(val(x),o,val(y))
original=values['out'];assert original==2118908950514353078
# A child may be deleted iff its only consumer is the selected parent; count
# consumer nodes (not edge multiplicity), allowing the parent to use it twice.
uses={n:set() for n,_,_,_ in rows}
for n,o,x,y in rows:
 for x0 in (x,y):
  if x0 in uses:uses[x0].add(n)
prior=list(range(-4,5))+g['witnesses']+g['fixed_numerals'];count=0;pairs=[];survivors=0;computed=0
for ix,(name,oldop,x,y) in enumerate(rows):
 children={a for a in (x,y) if isinstance(a,str) and a in uses and uses[a]=={name}}
 if children:
  # Only downstream descendants can change after substituting this node.
  affected={name};suffix=[]
  for r in rows[ix+1:]:
   n2,_,a,b=r
   if a in affected or b in affected:suffix.append(r);affected.add(n2)
  assert 'out' in affected
  for child in sorted(children):
   pairs.append((name,child));pool=[a for a in prior if a!=child];cache={}
   for a in pool:
    for b in pool:
     for operator in ('+','-','*'):
      count+=1;new_value=op(val(a),operator,val(b))
      if new_value not in cache:
       state={name:new_value}
       for n2,o2,a2,b2 in suffix:
        left=state.get(a2,val(a2)) if isinstance(a2,str) else a2
        right=state.get(b2,val(b2)) if isinstance(b2,str) else b2
        state[n2]=op(left,o2,right)
       cache[new_value]=state['out'];computed+=1
      if cache[new_value]==original:survivors+=1
 prior.append(name)
assert len(pairs)==55 and count==1084128 and survivors==0
print(json.dumps({'scope':'one explicit modular counterexample for each listed-class local output identity; no zero-equivalence or minimality claim',
 'operations':79,'modulus':mod,'natural_witness':witness,'port_raw_sha256':port_hashes,
 'original_output_residue':original,'eligible_parent_child_pairs':len(pairs),'candidate_tuples':count,
 'distinct_suffix_evaluations':computed,'equal_output_modulus_survivors':survivors,
 'coefficient_source':'external P72 bytes with matching P115 raw/gzip hashes','lean_elaboration':False},sort_keys=True,indent=2))
