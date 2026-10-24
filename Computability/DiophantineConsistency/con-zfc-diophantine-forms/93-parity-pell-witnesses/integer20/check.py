#!/usr/bin/env python3
"""Read-only exact certificate; deliberately does not import build.py."""
import ast, collections, gzip, hashlib, json, sys
from pathlib import Path
from parent_ring import Ring, need
ROOT=Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()

def interpret(expr,ring,vals):
 def go(node):
  if isinstance(node,ast.Name):return vals[node.id]
  if isinstance(node,ast.Constant) and type(node.value) is int:return ring.constant(node.value)
  if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return ring.add({},go(node.operand),-1)
  if isinstance(node,ast.BinOp):
   p=go(node.left)
   if isinstance(node.op,ast.Pow):
    need(isinstance(node.right,ast.Constant) and type(node.right.value) is int and 0<=node.right.value<=32,'polynomial exponent')
    return ring.power(p,node.right.value)
   q=go(node.right)
   if isinstance(node.op,ast.Add):return ring.add(p,q)
   if isinstance(node.op,ast.Sub):return ring.add(p,q,-1)
   if isinstance(node.op,ast.Mult):return ring.mul(p,q)
  raise ValueError('nonpolynomial syntax')
 return go(ast.parse(expr,mode='eval').body)

def dag_at(graph,roots,ring,atoms):
 needed=set(roots)
 for name,op,a,b in reversed(graph['source']):
  if name in needed and name not in atoms:needed.update((a,b))
 vals=dict(atoms)
 for name,op,a,b in graph['source']:
  if name not in needed or name in atoms:continue
  p=ring.constant(a) if type(a) is int else vals[a]
  q=ring.constant(b) if type(b) is int else vals[b]
  vals[name]=ring.mul(p,q) if op=='*' else ring.add(p,q,-1 if op=='-' else 1)
 return [vals[x] for x in roots]

def main():
 packet=json.loads((ROOT/'equation.json').read_text())
 graph=json.loads((ROOT/'circuit.json').read_text())
 need(sha((ROOT/'parent/equation.json').read_bytes())=='53a82b6b385f254f7e8f2a04ed800fa33c7a9ac92bc0940a63742e8a199a1a7c','pinned parent bytes')
 parent=json.loads((ROOT/'parent/equation.json').read_text())
 names=packet['variables']+packet['fixed_numerals']; ring=Ring(names)
 vals={n:ring.symbol(n) for n in names}; base=dict(vals)
 for n,e in packet['abbreviations']:
  need(n not in vals,'unique register');vals[n]=interpret(e,ring,vals)
 rows=[interpret(e,ring,vals) for e in packet['residuals']]
 oldvals={n:vals[n] for n in parent['variables']+parent['fixed_numerals']}
 oldrows=[interpret(e,ring,oldvals) for e in parent['residuals']]
 D=interpret('V*V-(p+y)**2',ring,vals)
 expected=[rows[0],{},rows[1],rows[2],rows[3],rows[4],{},rows[5],ring.add(rows[6],ring.mul(rows[5],D),-1)]
 for i,(x,y) in enumerate(zip(oldrows[:9],expected)):need(x==y,'complete parent row identity '+str(i))
 told=interpret('eta*(k-eta)',ring,vals);vv=dict(vals,told=told)
 oldguard=interpret('d*told-(pair_root**2-d-told+1)**2-Pos',ring,vv)
 need(oldrows[9]==oldguard,'literal parent sign guard')
 delta=interpret('tnew-b*b*told-b*eta*(c-eta-k*b)',ring,vv)
 need(not delta,'exact rescaling identity')
 need(interpret('a-E-b',ring,vals)=={},'inverse b chart')
 need(interpret('q-F-alpha-C',ring,vals)=={},'inverse C chart')
 degrees=[ring.degree(p,packet['variables']) for p in rows]
 need(degrees==[4,5,8,8,5,8,9,8],'all exact residual degrees')
 top=ring.leading(rows[6],packet['variables'],9)
 need(top==ring.parse('-8*r**2*c**4*f*o*(c+y)'),'complete leading residual')
 need(ring.mul(top,top)==ring.parse('64*r**4*c**8*f**2*o**2*(c+y)**2'),'full degree eighteen form')
 need(len(packet['variables'])==20 and len(rows)==8,'counts')
 computed=dag_at(graph,graph['residuals'],ring,base)
 for i,(x,y) in enumerate(zip(computed,rows)):need(x==y,'DAG residual '+str(i))
 atom_names=['R'+str(i) for i in range(8)]; final_ring=Ring(atom_names)
 cuts={root:final_ring.symbol(n) for root,n in zip(graph['residuals'],atom_names)}
 final=dag_at(graph,[graph['output']],final_ring,cuts)[0]
 need(final==final_ring.parse('+'.join(n+'**2' for n in atom_names)),'sum-of-squares finalizer')
 avail=set(names);live={graph['output']}
 for name,op,a,b in graph['source']:
  need(name not in avail and op in ['+','-','*'],'topology unique names')
  need(all(type(t) is int or t in avail for t in [a,b]),'topological operands')
  avail.add(name)
 for name,op,a,b in reversed(graph['source']):
  need(name in live,'all listed gates live');live.update((a,b))
 need(all(n in live for n in names),'all witnesses and coefficient ports live')
 need(len(graph['source'])==115==graph['operations'],'live arithmetic count')
 binding=json.loads((ROOT/'parent/coefficients/BINDING.json').read_text())
 values={};payloads={}
 for name,entry in binding['payloads'].items():
  packed=(ROOT/'parent/coefficients'/entry['file']).read_bytes();raw=gzip.decompress(packed)
  need(sha(packed)==entry['gzip_sha256'] and sha(raw)==entry['raw_sha256'],'coefficient byte binding '+name)
  value=int.from_bytes(raw,'little');values[name]=value
  need(len(raw)==entry['raw_bytes'] and value.bit_length()==entry['bits'],'minimal coefficient size '+name)
  payloads[name]=dict(raw_bytes=len(raw),bits=value.bit_length(),raw_sha256=sha(raw))
 need(values['beta']==(1<<1064921)-1 and values['beta']>1,'nonzero q numeral hypothesis')
 need(values['cone_A']==1<<1113 and values['cone_B']==1<<666104,'determinant scales')
 need(sum(e['raw_bytes'] for e in payloads.values())==615883,'coefficient total')
 receipt=dict(status='PASS',variables=20,equations=1,residuals=8,exact_degree=18,
  residual_degrees=degrees,operations=115,operation_breakdown=dict(collections.Counter(x[1] for x in graph['source'])),
  exact_parent_arithmetic_identities=9,parent_guard_bound=True,scaled_sign_identity=True,
  full_leading_form=packet['leading_form'],actual_payloads=payloads,
  proof_boundary='Finite exact algebra and coefficient checks; universal sign lemma and inherited unbounded calibration are in PROOF.md.',
  shared_engine='parent_ring.py is the unmodified upstream sparse-ring implementation; this is not an independently implemented algebra engine.')
 target='CHECKS_OPTIMIZED.json' if not __debug__ else 'CHECKS.json'
 (ROOT/target).write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:receipt[k] for k in ['status','variables','exact_degree','operations','operation_breakdown']},indent=2))

if __name__=='__main__':main()
