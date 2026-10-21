#!/usr/bin/env python3
"""Render frozen K215 decoder data into kernel-checked Lean literals.
No generator output is a trusted proof: Lean checks every finite block.
The finite incoming product is used as data, with new independent binding.
"""
import argparse, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def bb(b): return 'true' if b else 'false'
def lst(x):return '['+', '.join(bb(int(a)) for a in x)+']'
def act(a):return '⟨'+f'{bb(a[0])}, {a[1] if a[1]>=0 else "("+str(a[1])+")"}, {a[2]}'+ '⟩'

def generate():
 inp=ROOT/'inputs';cert=json.loads((inp/'decoder_context_certificate.json').read_text())
 assert sha(inp/'k215.native.tm')=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 assert sha(inp/'sites215.json')=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 T={}
 for s in (inp/'k215.native.tm').read_text().splitlines():
  if not s or s.startswith('#'):continue
  q,b,w,d,z=s.split();key=(int(q),int(b));assert key not in T
  T[key]=(int(w),1 if d=='R' else -1,int(z))
 assert len(T)==430
 nodes=cert['nodes'];roles=cert['roles'];blocks=[];idx={};edges={};traces=[]
 def expand(i,p):
  n=nodes[i]
  if isinstance(n[0],str):return [[p,*n]]
  assert 0<=n[0]<i and 0<=n[1]<i
  return expand(n[0],p+'0')+expand(n[1],p+'1')
 assert expand(cert['source_root'],'')==json.loads((inp/'sites215.json').read_text())
 for i,r in enumerate(roles):
  for b,e in enumerate(r['edges']):
   if e['kind']=='primitive':continue
   before={j-len(r['suffix']):int(v) for j,v in enumerate(r['suffix'])};before[0]=b
   tape=before.copy();q=r['state'];h=0;mn=0;trace=[]
   for _ in range(e['steps']):
    assert h in tape
    mn=min(mn,h);v=tape[h];w,d,z=T[q,v];trace.append([q,h,v,w,d,z]);tape[h]=w;h+=d;q=z
   assert h==1 and q==roles[e['role']]['state'] and tape==before
   word=(r['suffix']+str(b))[-(1-mn):]
   key=(r['state'],q,word,e['steps'])
   if key not in idx: idx[key]=len(blocks);blocks.append(key);traces.append(trace)
   edges[i,b]=idx[key]
 assert len(blocks)==281
 out=['import DecoderCertificate','','set_option maxHeartbeats 0','set_option maxRecDepth 10000','','namespace K215Decoder','open FramedWindow DecoderCertificate','','def nativeRows : Array (Option (Action × Action)) := #[']
 for q in range(max(q for q,b in T)+1):
  out.append('  '+('some ('+act(T[q,0])+', '+act(T[q,1])+')' if (q,0) in T else 'none')+',')
 out[-1]=out[-1].removesuffix(',');out+= [']','','def native : Table := fun q b => do','  let pair ← (nativeRows[q]?).join','  return if b then pair.2 else pair.1','','def sourceNodes : Array Node := #[']
 opmap={'CI':0,'CD':1,'CB':2,'CC':3,'CH':4}
 for n in nodes:
  out.append('  '+(f'.leaf {opmap[n[0]]} {n[1] or 0}' if isinstance(n[0],str) else f'.fork {n[0]} {n[1]}')+',')
 out[-1]=out[-1].removesuffix(',');out+= [']','','def blocks : Array Block := #[']
 for q,z,w,n in blocks:out.append(f'  ⟨{q}, {z}, {lst(w)}, {n}⟩,')
 out[-1]=out[-1].removesuffix(',');out+= [']','','def roles : Array Role := #[']
 for i,r in enumerate(roles):
  es=[]
  for b,e in enumerate(r['edges']):
   es.append(f'(.internal {e["role"]} {edges[i,b]})' if e['kind']=='internal' else f'(.primitive {e["node"]} {act(e["action"])})')
  out.append(f'  ⟨{r["node"]}, {r["state"]}, {lst(r["suffix"])}, {es[0]}, {es[1]}⟩,')
 out[-1]=out[-1].removesuffix(',');out+= [']','',f'def sourceRoot : Nat := {cert["source_root"]}','',
 'theorem working_states : nativeRows.toList.countP Option.isSome = 215 := by decide +kernel',
 'theorem counts : blocks.size = 281 ∧ roles.size = 234 ∧ sourceNodes.size = 202 := by decide +kernel',
 'theorem all_blocks_checked : blocks.toList.all (blockCheck native) = true := by decide +kernel',
 'theorem structure_checked : structuralCheck native sourceNodes roles blocks sourceRoot = true := by decide +kernel','',
 'theorem restores_arbitrary_tape (b : Block) (hb : b ∈ blocks.toList)',
 '    (a : Int) (t : Tape)',
 '    (hm : overlay (cells b.word) (fun i => t (i+a)) = (fun i => t (i+a))) :',
 '    0 < b.steps ∧',
 '    run (fullStep native) b.steps ⟨b.entry,a,t⟩ = some ⟨b.exit,a+1,t⟩ :=',
 '  all_blocks_sound native blocks.toList all_blocks_checked b hb a t hm','',
 '/-- These negative controls are checked by the same Lean kernel evaluator. -/',
 'theorem rejects_empty_window : check native 1 84 0 [] 0 1 = false := by decide +kernel',
 'theorem rejects_zero_duration : blockCheck native {blocks[0]! with steps := 0} = false := by decide +kernel',
 'theorem rejects_bad_exit : blockCheck native {blocks[0]! with exit := 999} = false := by decide +kernel','',
 'theorem certifies_block_chains (t : Tape) {q q2 : Nat} {a a2 : Int} {n : Nat}',
 '    (h : Chain blocks.toList t q a q2 a2 n) :',
 '    run (fullStep native) n ⟨q,a,t⟩ = some ⟨q2,a2,t⟩ :=',
 '  chain_sound native blocks.toList all_blocks_checked t h','',
 'theorem certificate_checked : blocks.toList.all (blockCheck native) = true ∧',
 '    structuralCheck native sourceNodes roles blocks sourceRoot = true :=',
 '  ⟨all_blocks_checked, structure_checked⟩','',
 '#print axioms all_blocks_checked','#print axioms structure_checked','#print axioms restores_arbitrary_tape',
 'end K215Decoder','']
 (ROOT/'K215Decoder.lean').write_text('\n'.join(out))
 proof={'table_sha256':sha(inp/'k215.native.tm'),'source_sha256':sha(inp/'sites215.json'),'incoming_certificate_sha256':sha(inp/'decoder_context_certificate.json'),'source_nodes':len(nodes),'expanded_primitive_occurrences':4751,'internal_occurrences':4750,'context_roles':len(roles),'internal_edges':371,'primitive_entry_edges':97,'minimal_window_blocks':len(blocks),'max_steps':max(n for q,z,w,n in blocks),'blocks':[{'entry':q,'exit':z,'word':w,'steps':n,'trace':traces[i]} for i,(q,z,w,n) in enumerate(blocks)]}
 (ROOT/'generation.json').write_text(json.dumps(proof,indent=2)+'\n')
 print(json.dumps({k:v for k,v in proof.items() if k!='blocks'},indent=2))
if __name__=='__main__': generate()
