from pathlib import Path
import json,re,ast,importlib.util,hashlib
here=Path(__file__).resolve().parent;repo=here.parents[2]; upstream=repo/'jamesyc-upstream/pa196';source=repo/'pa196-vs-u208/source-search/scan_rotations.py'
spec=importlib.util.spec_from_file_location('rot',source);rot=importlib.util.module_from_spec(spec);spec.loader.exec_module(rot)
v_spec=importlib.util.spec_from_file_location('cleanup',repo/'pa196-vs-u208/source-search/verify_second_cleanup.py');v=importlib.util.module_from_spec(v_spec);v_spec.loader.exec_module(v)
labels=ast.literal_eval(re.search(r'^def labels : List Nat := (\[.*\])$',(upstream/'PA196/Conjugacy.lean').read_text(),re.M).group(1))
if not (len(labels)==197 and labels[0]==74 and labels[75]==84 and labels[196]==254): raise ValueError('Conjugacy labels')
raw=(upstream/'data/pa196.tm').read_text();lines=['#! start 74'];
for row in raw.splitlines():
 q,b,w,d,t=row.split();lines.append(f'{labels[int(q)]} {b} {w} {d} {labels[int(t)]}')

if (here/'pa196.native.tm').read_text() != '\n'.join(lines)+'\n': raise ValueError('Native table does not match upstream')
for variant in ['original','one','two','both']:
 root=rot.root
 if variant in ('one','both'):root=v.patch(rot,root,v.PARENT_FIRST,('dec',1),[3773,3774,3775])
 if variant in ('two','both'):root=v.patch(rot,root,v.PARENT_SECOND,('dec',6),[7,8])
 ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
 rows=[[''.join(map(str,path)),ops[rot.store[leaf][0]],None if rot.store[leaf][0]=='halt' else rot.store[leaf][1]] for path,leaf in rot.leaf_occurrences(root)]

 if (here/f'{variant}.json').read_text() != json.dumps(rows,separators=(',',':'))+'\n': raise ValueError('Source JSON mismatch: '+variant)
 print(variant,'source leaf',len(rows),'node',rot.metric(root))
