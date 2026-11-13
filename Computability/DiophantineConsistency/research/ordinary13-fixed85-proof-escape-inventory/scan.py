from pathlib import Path
from hashlib import sha256
from collections import Counter
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-proof-escape-inventory')
selpath=Path('research/ordinary13-fixed85-source-selection-plan/selection.json');raw=selpath.read_bytes()
assert sha256(raw).hexdigest()=='f2d2503f011421235874a483b23026b846339bf1d736764b35527a45e02f0d83'
selection=json.loads(raw)['selected_modules'];assert len(selection)==1354
markers=('sorry','admit','axiom','unsafe','sorryAx','native_decide','run_tac','implemented_by','opaque','partial','postulate','ofReduceBool')
pat=re.compile(r'(?<![A-Za-z0-9_\'])(?:'+ '|'.join(map(re.escape,markers))+r')(?![A-Za-z0-9_\'])')
def blank_region(out,s,a,b):
 for i in range(a,b):
  if s[i]!='\n':out[i]=' '
def strip(s):
 out=list(s);i=0; comments=[];strings=[];interpolated=0
 while i<len(s):
  if s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;comments.append(s[i:j]);blank_region(out,s,i,j);i=j
  elif s.startswith('/-',i):
   start=i;i+=2;depth=1
   while i<len(s) and depth:
    if s.startswith('/-',i):depth+=1;i+=2
    elif s.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   assert depth==0,'unterminated nested block comment';comments.append(s[start:i]);blank_region(out,s,start,i)
  elif s[i]=='"':
   start=i
   if i>=2 and s[i-2:i]=='s!':interpolated+=1
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
   else:raise AssertionError('unterminated string')
   strings.append(s[start:i]);blank_region(out,s,start,i)
  elif s[i]=="'" and (i==0 or not (s[i-1].isalnum() or s[i-1] == "_")):
   # Skip common Lean character literals; identifier prime remains code.
   j=i+1
   if j<len(s) and s[j]=='\\':j+=2
   else:j+=1
   if j<len(s) and s[j]=="'":blank_region(out,s,i,j+1);i=j+1
   else:i+=1
  else:i+=1
 return ''.join(out),comments,strings,interpolated
# Synthetic lexer controls: nested comments and quoted strings cannot become
# code hits, while actual code markers remain visible.
fixture='theorem t : True := by sorry\n-- admit\n/- axiom /- unsafe -/ -/\n#eval "sorry"\nunsafe def f := 1\n'
clean,comments,strings,_=strip(fixture)
assert [m.group() for m in pat.finditer(clean)]==['sorry','unsafe']
assert any('admit' in x for x in comments) and any('sorry' in x for x in strings)
hits=[];excluded=Counter();counts=Counter();by_module=Counter();interpolated=0;raw_prefixes=0
for module,entry in sorted(selection.items()):
 p=Path(entry['source_path']); raw=p.read_bytes();assert sha256(raw).hexdigest()==entry['sha256'],module
 source=raw.decode();raw_prefixes+=len(re.findall(r'(?<![A-Za-z0-9_])r#+"',source));code,comments,strings,interp=strip(source);interpolated+=interp
 for what,blocks in [('comment',comments),('string',strings)]:
  for block in blocks:
   for x in pat.finditer(block):excluded[what+':'+x.group()]+=1
 lines=source.splitlines()
 for m in pat.finditer(code):
  tok=m.group();line=source.count('\n',0,m.start())+1;col=m.start()-(source.rfind('\n',0,m.start())+1)+1
  text=lines[line-1].strip();prefix=code[max(0,m.start()-1):m.start()];suffix=code[m.end():m.end()+1]
  # A token is syntactically present in code; a true declaration/escape or
  # tactic execution requires Lean parsing and proof/axiom checking.
  cls='code_lexical_token'
  if tok=='axiom' and re.search(r'^(?:private\s+|protected\s+|noncomputable\s+)*axiom\s+',text):cls='possible_axiom_declaration'
  if prefix=='.' or prefix=='«' or suffix=='»':cls='qualified_or_quoted_token'
  hits.append({'module':module,'source':str(p),'source_sha256':entry['sha256'],'line':line,'column':col,'token':tok,'classification':cls,'source_line':text[:240]})
  counts[tok]+=1;by_module[module]+=1
 # Separate markers: explicit constant declarations and Classical.choice.
 # The latter is a foundational/classical usage, not automatically an escape.
 for m in re.finditer(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*constant\s+[A-Za-z_]',code):
  at=code.find('constant',m.start(),m.end());line=source.count('\n',0,at)+1;col=at-(source.rfind('\n',0,at)+1)+1
  hits.append({'module':module,'source':str(p),'source_sha256':entry['sha256'],'line':line,'column':col,'token':'constant','classification':'possible_constant_declaration','source_line':lines[line-1].strip()[:240]})
  counts['constant']+=1;by_module[module]+=1
 for m in re.finditer(r'(?<![A-Za-z0-9_])Classical\.choice(?![A-Za-z0-9_])',code):
  line=source.count('\n',0,m.start())+1;col=m.start()-(source.rfind('\n',0,m.start())+1)+1
  hits.append({'module':module,'source':str(p),'source_sha256':entry['sha256'],'line':line,'column':col,'token':'Classical.choice','classification':'foundational_classical_marker','source_line':lines[line-1].strip()[:240]})
  counts['Classical.choice']+=1;by_module[module]+=1
inventory={'selection_sha256':sha256(selpath.read_bytes()).hexdigest(),
 'selected_module_count':len(selection),'markers':list(markers),'additional_scans':['constant command at line start','Classical.choice qualified occurrence'],'code_hits':hits,
 'comment_and_string_marker_counts':dict(sorted(excluded.items())),
 'interpolated_string_count':interpolated,'raw_string_prefix_occurrences':raw_prefixes,
 'scope':'Selected 1354 local source bytes only. Lexical token inventory, not Lean parser, provider/object, compiled axiom, tactic-execution or proof-soundness audit; interpolation/raw strings and quotation semantics are not resolved.'}
out=(json.dumps(inventory,sort_keys=True,indent=2)+'\n').encode();target=D/'inventory.json'
if sys.argv[1:]==['--write']:target.write_bytes(out)
else:assert not sys.argv[1:] and target.read_bytes()==out
print(json.dumps({'inventory_sha256':sha256(out).hexdigest(),'selected_modules_scanned':len(selection),'code_token_counts':dict(sorted(counts.items())),'modules_with_code_hits':len(by_module),'possible_axiom_declarations':sum(h['classification']=='possible_axiom_declaration' for h in hits),'possible_constant_declarations':sum(h['classification']=='possible_constant_declaration' for h in hits),'comment_and_string_marker_counts':dict(sorted(excluded.items())),'interpolated_string_count':interpolated,'raw_string_prefix_occurrences':raw_prefixes,'scanner_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'lean_executed':False,'scope':'Bounded local lexical inventory only; no actual axiom or proof audit.'},sort_keys=True,indent=2))
