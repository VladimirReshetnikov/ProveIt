#!/usr/bin/env python3
"""Static alignment check for the uncompiled 60-gate final-assignment draft."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];G=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';S=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(G)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(S)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23';g=json.loads(G.read_text());d=json.loads(S.read_text());src=(P/'NormAssignment38.lean').read_text();assert 'UNCOMPILED DRAFT' in src
lines=[x for x in src.splitlines() if re.match(r'^  let a\d+ : SignedPair S := ',x)];assert len(lines)==81
for i in range(14):assert lines[i]==f'  let a{i} : SignedPair S := ⟨w {i} + 1, 0⟩'
for i in range(4):assert lines[14+i]==f'  let a{14+i} : SignedPair S := ⟨ports {i}, 0⟩'
for i,n in enumerate((1,3,4)):assert lines[18+i]==f'  let a{18+i} : SignedPair S := ⟨{n}, 0⟩'
indices={n:i for i,n in enumerate(g['witnesses'])};indices.update({n:14+i for i,n in enumerate(g['fixed_numerals'])});indices.update({1:18,3:19,4:20});expected_gates=[];cut=inline=0
for off,(row,rec) in enumerate(zip(g['source'][:60],d['gate_records'])):
 n,op,a,b=row;assert (n,op,a,b)==(rec['name'],rec['op'],rec['left'],rec['right']);j=21+off;assert a in indices and b in indices and indices[a]<j and indices[b]<j
 tag={'+':'add','-':'sub','*':'mul'}[op];expected_gates.append((j,indices[a],indices[b],tag))
 if rec['kind']=='materialized':
  cut+=1;pos=rec['positive_coordinate']-1;neg=rec.get('negative_coordinate');rhs=f'⟨w {pos}, '+(f'w {neg-1}' if neg is not None else '0')+'⟩'
 else:assert rec['kind'] in ('inline','norm');inline+=1;rhs=f'pairCompute GateOp.{tag} a{indices[a]} a{indices[b]}'
 assert lines[j]==f'  let a{j} : SignedPair S := {rhs}',n;indices[n]=j
actual=[(int(a),int(b),int(c),op) for a,b,c,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',src)];assert actual==expected_gates and len(actual)==60 and (cut,inline)==(19,41)
assert '  !['+', '.join('a'+str(i) for i in range(81))+']' in src
for n,i in [('N0',61),('N1',44),('Na',78),('Nt',66),('scaled_Ns',80),('Delta',36)]:assert indices[n]==i
for pair in ['(v 61) = 1','(v 44) = 1','(v 78) = 1','(v 66) = 1','(v 80) = pairValue embed (v 36)']:assert pair in src,pair
for f in ['SharingNormTrace.lean','SharingNormSquares.lean']:
 x=(P/f).read_text();assert 'UNCOMPILED DRAFT' in x and 'sorry' not in x and 'admit' not in x
print(json.dumps({'status':'PASS_STATIC_ASSIGNMENT_ALIGNMENT','node_count':81,'graph_gates':60,'materialized_gates':cut,'inline_or_norm_gates':inline,'terminal_indices':{n:indices[n] for n in ('N0','N1','Na','Nt','scaled_Ns','Delta')},'source_sha256':sha(P/'NormAssignment38.lean'),'scope':'Source/seed transcription only; no Lean compilation, no model or iPRA proof.'},indent=2,sort_keys=True))
