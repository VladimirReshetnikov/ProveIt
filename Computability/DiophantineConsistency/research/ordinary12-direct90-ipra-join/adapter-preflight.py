#!/usr/bin/env python3
"""Static serialized-header impact analysis; not a final-provider audit."""
from pathlib import Path
from hashlib import sha256
import json,re,sys,time
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1];B=D/'research/ordinary12-ipra-bridge';ROOT=D.parents[1]
I=B/'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
C=B/'compact12-ipra-expanded-cone-rebuild-stage317-source-retry/cone-repinned.json'
OUT=H/'observations/adapter-preflight01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
need(not OUT.exists(),'refusing overwrite')
need(sha(I)=='bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2','inventory drift')
need(sha(C)=='eb5a8a3c8efb7b1d936d4c77ba2c6d201aff6d03f23c9e1697dd2b518aefcbf2','cone drift')
i=json.loads(I.read_text());c=json.loads(C.read_text());g=i['imports'];cone=set(c['topological_candidate'])
need(i['complete'] and len(cone)==425,'incomplete inputs')
roots=['DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.HAExpressionAssembly',
       'DiophantineConsistency.IPRAStandardTheory','DiophantineConsistency.IPRAReferenceInductionConversion',
       'DiophantineConsistency.AdaptiveEquationSyntax2011']
def closure(root):
 seen=set();outside=set();todo=[root]
 while todo:
  x=todo.pop()
  if x in seen or x in outside:continue
  if x not in g:outside.add(x);continue
  seen.add(x);todo.extend(g[x])
 affected=seen&cone
 while True:
  more=affected|{x for x in seen if any(y in affected for y in g[x])}
  if more==affected:break
  affected=more
 return {'selected_ancestors':sorted(seen),'outside_inventory':sorted(outside),
         'cone_ancestors':sorted(seen&cone),'affected_outside_cone':sorted(affected-cone)}
r={x:closure(x) for x in roots}
order=['DiophantineConsistency.IPRASuccessorInduction','DiophantineConsistency.IPRAAddOneGeneral',
       'DiophantineConsistency.IPRASuccessorInductionConverse','DiophantineConsistency.IPRAStandardTheory']
need(set(r[roots[2]]['affected_outside_cone'])==set(order),'unexpected affected standard cone')
need(not r[roots[3]]['cone_ancestors'],'reference conversion reaches cone')
rows=[]
for n in order:
 f=D/'Lean'/Path(n.replace('.','/')+'.lean');need(f.is_file(),'missing '+n)
 direct=[x for x in g[n] if x!='Init']
 source=re.findall(r'^import\s+(\S+)',f.read_text(),re.M)
 need(direct==source,'serialized/source direct imports differ '+n)
 rows.append({'module':n,'source':str(f.relative_to(ROOT)),'source_sha256':sha(f),
              'historical_object_sha256':i['objects'][n]['sha256'],'serialized_imports':g[n]})
need(all(dep not in order or order.index(dep)<idx for idx,row in enumerate(rows) for dep in row['serialized_imports']),
     'dependency order')
OUT.parent.mkdir(parents=True,exist_ok=False)
result={'time_ns':time.time_ns(),'inventory_sha256':sha(I),'cone_sha256':sha(C),'script_sha256':sha(__file__),
        'roots':r,'rebuild_order':rows,'scope':'historical selected serialized-header impact analysis; finalized actual provider and all outside/package/dynamic ancestry not authenticated'}
OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','roots':{n:{'selected':len(x['selected_ancestors']),'cone':len(x['cone_ancestors']),
 'affected_outside_cone':len(x['affected_outside_cone'])} for n,x in r.items()},'rebuild':[x['module'] for x in rows]},indent=2))
