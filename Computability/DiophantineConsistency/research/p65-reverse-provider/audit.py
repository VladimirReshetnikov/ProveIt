from pathlib import Path
import hashlib,json,re,sys
base=Path('/tmp/p65-reverse-provider'); m=json.loads((base/'manifest.json').read_text()); r=json.loads((base/'results.json').read_text());errors=[]; warnings=[]
if len(r)!=len(m['order']):errors.append(f'incomplete objects: {len(r)}/{len(m["order"])}')
for e in m['order']:
 name=e['module'];src=Path(e['original']).read_text()
 if re.search(r'\b(sorry|admit)\b',src):errors.append('source placeholder: '+name)
 result=r.get(name)
 if not result:errors.append('no result: '+name);continue
 for key,hashkey in [('object','object_sha256'),('log','log_sha256')]:
  p=Path(result[key]);actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
  if actual!=result[hashkey]:errors.append(f'{name}: {key} hash mismatch')
 if result['shim_sha256']!=e['shim_sha256']:errors.append('shim mismatch '+name)
 log=Path(result['log']).read_text()
 if 'exit: 0,' not in log:errors.append('nonzero compiler exit '+name)
 if re.search(r'\bsorryAx\b|\berror:',log):errors.append('error/sorryAx in '+name)
 for ln in log.splitlines():
  if 'warning:' in ln:
   if name.endswith('.FreeJPowerCancel') and 'Variable name `hv` is not explicitly referenced' in ln:warnings.append(ln)
   else:errors.append('unexpected warning: '+ln)
  if 'depends on axioms:' in ln:
   match=re.search(r'depends on axioms: \[(.*?)\]',ln)
   if not match or any(x.strip() not in {'propext','Classical.choice','Quot.sound'} for x in match.group(1).split(',')):
    errors.append('unexpected axioms: '+ln)
print('objects:',len(r),'/',len(m['order']))
for warning in warnings:print('benign warning:',warning)
for error in errors:print('ERROR:',error)
if errors:sys.exit(1)
print('reverse provider audit passed')
