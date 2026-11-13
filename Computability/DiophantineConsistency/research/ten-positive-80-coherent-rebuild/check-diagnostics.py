#!/usr/bin/env python3
"""Read-only mutation check of the v3 diagnostic rejection pattern."""
import ast, json, re
from hashlib import sha256
from pathlib import Path
H=Path(__file__).resolve().parent
SOURCE=H/'run-v3.py'
tree=ast.parse(SOURCE.read_text())
patterns=[]
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and node.func.attr=='search' and node.args:
  arg=node.args[0]
  if isinstance(arg,ast.Constant) and isinstance(arg.value,str) and 'sorryAx' in arg.value:
   patterns.append(arg.value)
if len(patterns)!=1:raise RuntimeError('expected exactly one diagnostic pattern')
pattern=patterns[0]
positive=['error: failed','warning: unused','error(lean.foo): failed','warning(lean.foo): unused',
          'x:10:2: warning(lean.unusedSimpArgs): unused','ERROR(lean.name): failed',
          "depends on axioms: [sorryAx]"]
negative=['no diagnostic','an error bound in the proof','a warning policy is strict',
          "depends on axioms: [propext, Classical.choice, Quot.sound]"]
if any(not re.search(pattern,s) for s in positive):raise RuntimeError('missed diagnostic')
if any(re.search(pattern,s) for s in negative):raise RuntimeError('false positive')
print(json.dumps({'status':'PASS','source_sha256':sha256(SOURCE.read_bytes()).hexdigest(),
                  'pattern':pattern,'positive':len(positive),'negative':len(negative)},sort_keys=True))
