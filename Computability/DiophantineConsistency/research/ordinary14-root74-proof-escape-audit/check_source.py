#!/usr/bin/env python3
"""Bounded lexical source scan; never invokes Lean or computes axiom closure."""
from pathlib import Path
import collections,hashlib,json,re
P=Path(__file__).resolve().parent;D=P.parents[1]
raw_inv=D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json'
slim_inv=D/'research/ordinary14-root74-slim-overlay/inventory.json'
H=lambda b:hashlib.sha256(b).hexdigest()
assert H(raw_inv.read_bytes())=='2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7'
assert H(slim_inv.read_bytes())=='b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'
a=json.loads(raw_inv.read_bytes());b=json.loads(slim_inv.read_bytes());assert (a['draft_count'],a['qualified_direct_count'],b['draft_count'])==(159,31,159)
tokens=('sorry','admit','axiom','unsafe','native_decide','run_tac','implemented_by','ofReduceBool','trustCompiler','partial','unsafeCast','sorryAx','panic!','unreachable!')
pattern=re.compile(r"(?<![A-Za-z0-9_'])"+'(?:'+'|'.join(re.escape(x) for x in tokens)+r")(?![A-Za-z0-9_'])")
selection=re.compile(r"(?<![A-Za-z0-9_'])Classical\.(?:choose!_eq_iff_right|choose_spec|choose!|choose|choice)(?![A-Za-z0-9_'])")
def scrub(text):
 # Preserve character positions/newlines while excluding nested comments,
 # line comments and ordinary escaped strings. Unsupported forms fail closed.
 assert 'r#"' not in text and 's!"' not in text and 'm!"' not in text and 'f!"' not in text
 out=[];i=0;depth=0;mode='code';escaped=False
 while i<len(text):
  c=text[i];pair=text[i:i+2]
  if mode=='block':
   if pair=='/-':out.extend('  ');depth+=1;i+=2;continue
   if pair=='-/':out.extend('  ');depth-=1;i+=2;mode='code' if depth==0 else mode;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if mode=='line':
   out.append('\n' if c=='\n' else ' ');i+=1
   if c=='\n':mode='code'
   continue
  if mode=='string':
   out.append('\n' if c=='\n' else ' ');i+=1
   if escaped:escaped=False
   elif c=='\\':escaped=True
   elif c=='"':mode='code'
   continue
  if pair=='/-':out.extend('  ');i+=2;depth=1;mode='block';continue
  if pair=='--':out.extend('  ');i+=2;mode='line';continue
  if c=='"':out.append(' ');i+=1;mode='string';continue
  assert c not in '«»', 'quoted identifier unsupported'
  out.append(c);i+=1
 assert mode not in ('block','string'),(mode,depth)
 return ''.join(out)
# Regression controls for nested comments, line comments and escaped strings.
test='-- sorry\n/- axiom /- native_decide -/ admit -/\n"unsafe \\\"sorry\\\""\nby sorry\n'
assert [m.group(0) for m in pattern.finditer(scrub(test))]==['sorry']
assert scrub(test).count('\n')==test.count('\n')
for token in tokens:
 assert [m.group(0) for m in pattern.finditer(scrub('by '+token+'\n'))]==[token],token
def scan(group,base):
 counts=collections.Counter();hits=[];choices=[];prints=[];hashes={}
 for r in group:
  path=base/r['path'];data=path.read_bytes();expected=r.get('overlay_sha256',r.get('sha256'));assert H(data)==expected,r['path'];hashes[r['path']]=H(data)
  text=scrub(data.decode())
  for m in pattern.finditer(text):
   token=m.group(0);counts[token]+=1;hits.append({'path':r['path'],'line':text.count('\n',0,m.start())+1,'token':token})
  for m in selection.finditer(text):choices.append({'path':r['path'],'line':text.count('\n',0,m.start())+1,'token':m.group(0)})
  for m in re.finditer(r'^\s*#print\s+axioms\b',text,re.M):prints.append({'path':r['path'],'line':text.count('\n',0,m.start())+1})
 return {'source_count':len(group),'escape_token_counts':dict(sorted(counts.items())),'escape_hits':hits,'classical_selection_lexical_hits':choices,'print_axioms_commands_not_executed':len(prints),'source_sha256':dict(sorted(hashes.items()))}
original=scan(a['drafts_topological'],D);qualified=scan(a['qualified_direct_sources'],D);overlay=scan(b['drafts_topological'],D/'research/ordinary14-root74-slim-overlay')
assert not original['escape_hits'] and not qualified['escape_hits'] and not overlay['escape_hits']
assert len(qualified['classical_selection_lexical_hits'])==4
print(json.dumps({'scope':'lexical tokens after basic comment/string scrubbing; no Lean parser, elaboration, transitive dependency or axiom closure','raw_inventory_sha256':H(raw_inv.read_bytes()),'slim_inventory_sha256':H(slim_inv.read_bytes()),'tokens':list(tokens),'scrubber_regression':'pass','original_bare_drafts':original,'direct_qualified_sources':qualified,'slim_overlay_drafts':overlay},sort_keys=True,indent=2))
