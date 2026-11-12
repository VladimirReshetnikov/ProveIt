#!/usr/bin/env python3
"""Bounded source token scan; no Lean, axiom or import-closure claim."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode): raise SystemExit("use python3 -I -S -B")
P=Path(__file__).resolve().parent
D=P.parents[1]
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

inventory=json.loads((P/'inventory.json').read_bytes())
test='-- sorry\n/- axiom /- native_decide -/ admit -/\n"unsafe"\nby sorry\n'
assert [m.group(0) for m in pattern.finditer(scrub(test))]==['sorry']
for token in tokens:
 assert [m.group(0) for m in pattern.finditer(scrub('by '+token+'\n'))]==[token]
hits=[]; choices=[]; prints=[]; unsupported=[]; verified=[]
for group in ('drafts_topological','qualified_direct_sources'):
 for row in inventory[group]:
  path=D/row['path']; raw=path.read_bytes(); assert hashlib.sha256(raw).hexdigest()==row['sha256']
  try: text=scrub(raw.decode())
  except (AssertionError,UnicodeError) as e:
   unsupported.append({'path':row['path'],'reason':str(e)}); continue
  verified.append(row['path'])
  for regex,collection in ((pattern,hits),(selection,choices)):
   for m in regex.finditer(text): collection.append({'path':row['path'],'line':text.count('\n',0,m.start())+1,'token':m.group(0)})
  for m in re.finditer(r'^\s*#print\s+axioms\b',text,re.M): prints.append({'path':row['path'],'line':text.count('\n',0,m.start())+1})
print(json.dumps({'scope':'lexical token inventory after bounded comment/string scrubbing; no Lean parser, axiom closure or transitive provider claim','inventory_sha256':hashlib.sha256((P/'inventory.json').read_bytes()).hexdigest(),'tokens':list(tokens),'scrubber_regression':'pass','checked_source_count':len(verified),'unsupported_files':unsupported,'escape_hits':hits,'classical_selection_hits':choices,'print_axioms_commands_not_executed':len(prints)},sort_keys=True,indent=2))
