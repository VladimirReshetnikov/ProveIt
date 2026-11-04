from pathlib import Path
import re,json,hashlib
root=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean')
out=Path('/tmp/p65-canonical-endpoint-provider')
providers=[Path('/tmp/p65-reverse-provider/lib'),Path('/tmp/trace74-direct-four-block-1zltaw2f/lib'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')]
seen=set(); build=[]; bindings={}; missing=[]
def digest(b):return hashlib.sha256(b).hexdigest()
def resolve(name):
 if name=='DiophantineConsistency.Compact44.P65Graph': return 'P65GraphShim'
 candidates=[name]
 if name.startswith('DiophantineConsistency.Compact44.'):
  suffix=name[len('DiophantineConsistency.Compact44.'):]
  candidates += [suffix,'DiophantineConsistency.'+suffix]
 for provider in providers:
  for candidate in candidates:
   obj=provider/(candidate.replace('.','/')+'.olean')
   if obj.is_file():
    bindings[name]={'provider_module':candidate,'object':str(obj),'sha256':digest(obj.read_bytes())}
    return candidate
 return name
def visit(name):
 if name in seen:return
 seen.add(name)
 target=resolve(name)
 if target != name or name in bindings or name.startswith(('Mathlib.','Foundation.','Batteries.','Lean.')):return
 src=root/(name.replace('.','/')+'.lean')
 if not src.is_file():missing.append(name);return
 data=src.read_bytes(); text=data.decode(); imports=re.findall(r'^import\s+(\S+)',text,re.M)
 for dep in imports:visit(dep)
 subs={dep:resolve(dep) for dep in imports}
 patched=re.sub(r'^(import\s+)(\S+)',lambda m: m.group(1)+subs[m.group(2)],text,flags=re.M)
 dest=out/'src'/(name.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(patched)
 build.append({'module':name,'original':str(src),'source_sha256':digest(data),'shim':str(dest),'shim_sha256':digest(patched.encode()),'imports':subs})
visit('DiophantineConsistency.Compact44.IPRAPositive65')
early={'DiophantineConsistency.Compact44.'+s for s in ['P65ConvZero','P72ConvZero','P72ConvArith','P72Converse','P65Converse']}
build=[x for x in build if x['module'] in early]+[x for x in build if x['module'] not in early]
manifest={'missing':missing,'bindings':bindings,'order':build,'note':'P65GraphShim object is an external captured dependency; exact source import edits only.'}
out.mkdir(exist_ok=True)
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(out/'build-order.txt').write_text('\n'.join(x['module'] for x in build)+'\n')
print('build order:',len(build),'provider bindings:',len(bindings),'missing:',missing)
