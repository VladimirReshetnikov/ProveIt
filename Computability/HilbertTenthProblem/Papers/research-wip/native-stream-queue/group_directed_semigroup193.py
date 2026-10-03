#!/usr/bin/env python3
"""Data-only, bounded CLI construction of the 193-generator U15 semigroup."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
from zipfile import ZipFile

ARCHIVE = 'Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip'
ARCHIVE_SHA256 = 'b494c2b8e516d811cbecf305a748197af2a565882319a86586fec316c5ba8c47'
PREFIX = 'universal-matrix-report32-release-20261003/'
PINS = {
 'core/PROOF.md':'8764c608e380132e6e226c7e2f7754bf591579bdbea1162511179677a0663794',
 'core/loader-audit/U15_DEPENDENCY_AUDIT.md':'e8121b79d24eabb025bf74b144cc6517f084b26992b2b9c4b4ace47c62f070f5',
 'core/data/semigroup.json':'506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9',
 'core/data/u15_table.json':'0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a',
 'core/evidence/accepting-witness.json':'13a3857d28b0207d9baa83facac5b2e67bbaeb858d00b82ef9a91c4ab38df890',
}
COPY = '01[]'
TERMINAL = '[J1]'
DELETED = list(range(3,18))+[20,108,113]

def need(ok, why):
 if not ok: raise ValueError(why)

def digest(b): return sha256(b).hexdigest()

def same(a,b):
 if type(a)is not type(b): return False
 if type(a)is dict: return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if type(a)is list: return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

def read(root):
 path=root/'docs/incoming'/ARCHIVE
 need(digest(path.read_bytes())==ARCHIVE_SHA256,'archive bytes')
 with ZipFile(path) as z:
  need(len(z.namelist())==len(set(z.namelist())),'unique member names')
  blobs={name:z.read(PREFIX+name) for name in PINS}
 for name,b in blobs.items(): need(digest(b)==PINS[name],'member '+name)
 return (json.loads(blobs['core/data/semigroup.json']),
         json.loads(blobs['core/data/u15_table.json']),
         json.loads(blobs['core/evidence/accepting-witness.json']))

def identity(n): return [[int(i==j) for j in range(n)] for i in range(n)]

def mm(a,b):
 n=len(a)
 return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

def inv(a):
 need(len(a)==2 and a[0][0]*a[1][1]-a[0][1]*a[1][0]==1,'SL2 inverse')
 return [[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]]

def det(a):
 n=len(a);total=0
 for p in permutations(range(n)):
  term=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
  for i,j in enumerate(p): term*=a[i][j]
  total+=term
 return total

def E(j): return [[1+4*j,2],[-8*j*j,1-4*j]]

def block(a,b):
 return [[a[i][j] if i<2 and j<2 else b[i-2][j-2] if i>=2 and j>=2 else 0 for j in range(4)] for i in range(4)]

def phi(word,codes):
 a=identity(2)
 for c in word: a=mm(a,E(codes[c]))
 return a

def target(word,codes): return block(inv(phi(word+'#',codes)),E(0))

def generate(old,table):
 need(list(table)==[q+a for q in 'ABCDEFGHIJKLMNO' for a in '01'],'literal table order')
 need([k for k,v in table.items() if v is None]==['J1'],'only halting cell')
 alphabet=list('01ABCDEFGHIJKLMNO[]X')
 need(old['alphabet']==alphabet and old['top_codes']=={**{a:i+1 for i,a in enumerate(alphabet)},'#':21},'unchanged top codes')
 machine=[]
 for cell,transition in table.items():
  if transition is None: continue
  b,d,p=transition
  need(type(b)is int and b in (0,1) and d in ('L','R') and p in alphabet[2:17],'transition')
  for ctx in ('0','1','boundary'):
   if d=='R': lhs=cell+(ctx if ctx!='boundary' else ']');rhs=str(b)+p+(ctx if ctx!='boundary' else '0]')
   else: lhs=(ctx if ctx!='boundary' else '[')+cell;rhs=(p+ctx if ctx!='boundary' else '['+p+'0')+str(b)
   machine.append(dict(id=len(machine)+1,kind='transition',cell=cell,context=ctx,lhs=lhs,rhs=rhs))
 need(len(machine)==87 and machine==old['rules'][:87],'every actual machine rule independently rebuilt')
 need(old['rules'][87]==dict(id=88,kind='halt',lhs='J1',rhs='X'),'deleted old halt')
 need(old['rules'][-1]==dict(id=93,kind='finish',lhs='[X]',rhs='X'),'deleted old finish')
 cleanup=[dict(r,lhs=r['lhs'].replace('X','J1'),rhs='J1') for r in old['rules'][88:92]]
 need([(r['lhs'],r['rhs']) for r in cleanup]==[('0J1','J1'),('J10','J1'),('1J1','J1'),('J11','J1')],'four literal halt-context erasures')
 rules=machine+cleanup;rulemap={r['id']:r for r in rules};tiles=[]
 need([t['id'] for t in old['tiles']]==list(range(1,115)),'actual old tile order')
 for t in old['tiles']:
  if t['id'] in DELETED: continue
  t=dict(t)
  if t['kind']=='rewrite':
   r=rulemap[t['rule_id']];t.update(h=r['rhs'],g=r['lhs'])
  tiles.append(t)
 need(len(tiles)==96 and Counter(t['kind'] for t in tiles)==dict(copy=4,rewrite=91,separator=1),'complete tile accounting')
 need([t['letter'] for t in tiles if t['kind']=='copy']==list(COPY),'only context copy letters')
 need(all(t['h'] and t['g'] and ('#' not in t['h']+t['g'] or t['kind']=='separator') for t in tiles),'nonempty sides and private separator')
 codes=old['top_codes'];t=E(0);generators=[]
 for side in ('A','B'):
  for tile in tiles:
   j=tile['id']
   top=phi(tile['h'],codes) if side=='A' else inv(phi(tile['g'],codes))
   bottom=E(j) if side=='A' else mm(mm(inv(t),inv(E(j))),t)
   generators.append(dict(name=side+str(j),tile_id=j,matrix=block(top,bottom)))
 generators.append(dict(name='C',tile_id=None,matrix=block(inv(phi(TERMINAL+'#',codes)),t)))
 # Every surviving lower matrix is unchanged; exactly the cleanup pairs and C change on top.
 oldmap={g['name']:g for g in old['generators']};changed=[]
 for g in generators:
  previous=oldmap[g['name']]
  need([r[2:] for r in g['matrix'][2:]]==[r[2:] for r in previous['matrix'][2:]],'unchanged lower code '+g['name'])
  if g['matrix']!=previous['matrix']: changed.append(g['name'])
 need(changed==['A109','A110','A111','A112','B109','B110','B111','B112','C'],'exact changed generator inventory')
 need(len(generators)==193 and len({tuple(sum(g['matrix'],[])) for g in generators})==193,'literal distinct array')
 need(all(det(g['matrix'])==1 for g in generators),'all complete SL4 determinants')
 entries=[a for g in generators for row in g['matrix'] for a in row]
 ledger=dict(states=15,tape_symbols=2,defined_transitions=29,machine_rules=87,halt_context_erasure_rules=4,halt_conversion_rules=0,bracket_erasure_rules=0,rules=91,copy_tiles=4,separator_tiles=1,inner_tiles=96,generators=193,matrix_dimension=4,active_rewrite_alphabet_size=19,active_top_alphabet_size=20,largest_retained_top_code=21,largest_retained_lower_code=114,matrix_entry_slots=len(entries),nonzero_entries=sum(a!=0 for a in entries),maximum_absolute_entry=max(map(abs,entries)),maximum_entry_magnitude_bits=max(abs(a).bit_length() for a in entries),sum_entry_magnitude_bits=sum(abs(a).bit_length() for a in entries),changed_retained_generators=len(changed),unchanged_retained_generators=193-len(changed))
 return dict(schema='literal-directed-u15-semigroup193-v1',terminal=TERMINAL,separator='#',alphabet=list('01ABCDEFGHIJKLMNO[]'),top_codes=codes,deleted_old_tile_ids=DELETED,rules=rules,tiles=tiles,generators=generators,ledger=ledger,changed_generators=changed)

def rewrite(word,rule,pos):
 need(type(pos)is int and 0<=pos<=len(word)-len(rule['lhs']) and word[pos:pos+len(rule['lhs'])]==rule['lhs'],'actual rewrite occurrence')
 return word[:pos]+rule['rhs']+word[pos+len(rule['lhs']):]

def witness(old,packet,saved):
 rules={r['id']:r for r in packet['rules']};tiles={t['id']:t for t in packet['tiles']};copies={t['letter']:t['id'] for t in packet['tiles'] if t['kind']=='copy'}
 oldrules={r['id']:r for r in old['rules']};original=saved['derivation'][0]
 need(len(saved['rewrite_steps'])==14 and len(saved['derivation'])==15,'pinned old derivation length')
 for before,after,(rid,pos) in zip(saved['derivation'],saved['derivation'][1:],saved['rewrite_steps']):need(rewrite(before,oldrules[rid],pos)==after,'all old witness steps')
 steps=[s for s in saved['rewrite_steps'] if s[0] not in (88,93)]
 need(len(steps)==12,'two obsolete steps removed')
 current=original;derivation=[current];inner=[];blocks=[]
 for rid,pos in steps:
  r=rules[rid];prefix=current[:pos];suffix=current[pos+len(r['lhs']):]
  need(all(c in COPY for c in prefix+suffix),'no omitted state-copy used')
  ids=[copies[c] for c in prefix]+[20+rid]+[copies[c] for c in suffix]+[114]
  current=rewrite(current,r,pos);derivation.append(current);inner+=ids;blocks.append(ids)
 need(current==TERMINAL,'new terminal reached')
 h=''.join(tiles[i]['h'] for i in inner);g=''.join(tiles[i]['g'] for i in inner)
 need(original+'#'+h==g+TERMINAL+'#','entire constrained word equation')
 names=['A'+str(i) for i in inner]+['C']+['B'+str(i) for i in reversed(inner)]
 gen={g['name']:g['matrix'] for g in packet['generators']};value=identity(4)
 for name in names:value=mm(value,gen[name])
 want=target(original,packet['top_codes'])
 need(value==want==saved['input']['target']==saved['product'],'all sixteen literal product entries and unchanged target')
 inp=saved['input'];need(original=='['+inp['left_nearest_first'][::-1]+'A0'+inp['right_nearest_first']+']','unchanged nearest-first input map')
 return dict(input=dict(inp),derivation=derivation,rewrite_steps=steps,rewrite_step_count=len(steps),inner_tile_blocks=blocks,inner_tile_sequence=inner,tile_count=len(inner),generator_word=names,generator_word_length=len(names),product=value)

def contexts(packet,table):
 words=[''.join(bits) for n in range(3) for bits in product('01',repeat=n)]
 rules=packet['rules'];machine={r['id']:r for r in rules if r['kind']=='transition'};clean={r['lhs']:r for r in rules if r['kind']!='transition'}
 checked=halted=erased=0
 for l,r in product(words,repeat=2):
  for q,a in product('ABCDEFGHIJKLMNO','01'):
   w='['+l+q+a+r+']';hits=[(row,pos) for row in rules for pos in range(len(w)) if w.startswith(row['lhs'],pos)]
   tr=table[q+a]
   if tr is None:
    need(all(row['id'] not in machine for row,pos in hits),'no machine rule at halt')
    halted+=1
   else:
    need(len(hits)==1 and hits[0][0]['id'] in machine,'no premature cleanup or foreign machine rule')
    b,d,p=tr
    expected='['+l+str(b)+p+(r if r else '0')+']' if d=='R' else '['+(l[:-1] if l else '')+p+(l[-1] if l else '0')+str(b)+r+']'
    need(rewrite(w,*hits[0])==expected,'actual finite-tape transition oracle')
   checked+=1
  current='['+l+'J1'+r+']'
  for b in l[::-1]: current=rewrite(current,clean[b+'J1'],len(current.split('J')[0])-1)
  for b in r: current=rewrite(current,clean['J1'+b],1)
  need(current==TERMINAL,'all tested binary contexts erased without brackets')
  erased+=1
 need(not any(r['lhs'] in TERMINAL for r in rules),'terminal irreducible')
 return dict(live_configurations=checked,halting_configurations=halted,cleanup_contexts=erased,context_side_lengths=[0,1,2])

def verify(root):
 old,table,saved=read(root);p=generate(old,table);w=witness(old,p,saved);checks=contexts(p,table)
 need(target('[J1]',p['top_codes'])==p['generators'][-1]['matrix'],'nonempty one-generator zero-step terminal product')
 return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),archive=dict(name=ARCHIVE,sha256=ARCHIVE_SHA256,prefix=PREFIX),member_pins=PINS,packet=p,accepting_witness=w,verification=dict(**checks,all_determinants=1,distinct_generators=193,complete_product_verified=True,word_equation_verified=True),scope='Fixed directed semigroup and unchanged finite-U15-input target map. All193 matrices literal. No subgroup/inverse closure, no general malformed-input forward correspondence, no Diophantine gate bound, no historical or archive code execution; published U15 universality remains an inherited mathematical dependency.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo-root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo_root)
 if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],ledger=r['packet']['ledger'],witness=dict(steps=r['accepting_witness']['rewrite_step_count'],tiles=r['accepting_witness']['tile_count'],generators=r['accepting_witness']['generator_word_length']),checks=r['verification'])))
if __name__=='__main__':main()
