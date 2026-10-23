from pathlib import Path
import json
p=Path(__file__).resolve().parent
x=json.loads((p/'FRONTIER_COUNTS.json').read_text());groups={}
for c in x['circuits']:
 d=c['reported_degree'];dom=c['domain'];dom='Z' if dom and ('unrestricted' in dom or dom in ['integers','Z']) else 'N+' if dom is None or ('positive' in dom) else dom
 if d is not None:groups.setdefault((dom,c['variables']),[]).append(c)
out=[]
for (dom,n),cs in groups.items():
 front=[c for c in cs if not any(t['reported_degree']<=c['reported_degree'] and t['operations']<=c['operations'] and (t['reported_degree']<c['reported_degree'] or t['operations']<c['operations']) for t in cs)]
 print(dom,n,sorted(set((c['reported_degree'],c['operations']) for c in front)));out.append({'domain':dom,'variables':n,'points':front})
(p/'SELECTED_PARETO.json').write_text(json.dumps({'scope':'Selected circuits only, no global minimum. Null source domains classified by packet documentation as strictly positive. Degrees imported from packet metadata and separately covered by original replays.','groups':out},indent=2)+'\n')
