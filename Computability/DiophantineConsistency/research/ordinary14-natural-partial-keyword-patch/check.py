#!/usr/bin/env python3
"""Check inert name replacements and selected parser sources; no Lean run."""
import hashlib,json,re,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode): raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent; D=P.parents[1]
lean=Path.home()/'.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Parser'
files={
 'parser_command':(lean/'Command.lean','e4afed93ed1a2de7d56df108f9d5963f0495489936f4bc4b48d6c9742c90ed03'),
 'parser_basic':(lean/'Basic.lean','52bc0d189a600e760fde91f55e1429d9a612b1a63452da063ee74de9ed3f3d8e'),
 'PartialShift82To74':(D/'research/ordinary14-natural-forced82-predecessor-draft/PartialShift82To74.lean','33b1d66bc3ab8010d83b91bff8604b015a3df000630a8d09fabbd77aa3e30a7e'),
 'GraphPredecessors82':(D/'research/ordinary14-natural-forced82-predecessor-draft/GraphPredecessors82.lean','7972ddb132643d0fd46bfd66e200bdf80a48e5d0df1b75f719b9c4ef5db5de54'),
 'patch_shift':(P/'PartialShift82To74.lean.src','47cb83c7a8cf4053e19eb7afbb391e00528b8b0ce5fdf4a2edda9c909163170e'),
 'patch_client':(P/'GraphPredecessors82.lean.src','44c47be7c5725bd5bbe11ed810780938c3b885eb394ae69d5bfc9797d8ce9c5e'),
}
s={}
for name,(path,digest) in files.items():
 data=path.read_bytes(); assert hashlib.sha256(data).hexdigest()==digest,name; s[name]=data.decode()
assert 'def «partial»        := leading_parser "partial "' in s['parser_command']
assert 'def declId := leading_parser\n  ident >>' in s['parser_command']
assert 'we want it to be recognized as a symbol' in s['parser_basic']
assert 'if isToken startPos stopPos tk then' in s['parser_basic']
pat=re.compile(r"(?<![A-Za-z0-9_'])partial(?![A-Za-z0-9_'])")
for name,patch,n in [('PartialShift82To74','patch_shift',8),('GraphPredecessors82','patch_client',7)]:
 count=0; out=[]
 for line in s[name].splitlines(keepends=True):
  if line.lstrip().startswith('/--'): out.append(line); continue
  line,k=pat.subn('partialValuation',line); count+=k; out.append(line)
 assert count==n and ''.join(out)==s[patch],name
print(json.dumps({'scope':'pinned parser-source inspection and inert textual alternatives; no Lean parse or elaboration','pinned_files':len(files),'code_identifier_replacements':{'PartialShift82To74':8,'GraphPredecessors82':7},'originals_unchanged':2},sort_keys=True,indent=2))
