from pathlib import Path
import difflib, json, re, hashlib
base=Path(__file__).resolve().parent
src=base.parent/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
out=base/'proposed';out.mkdir(exist_ok=True)
interval=(base/'IntervalPropagationCandidate.lean').read_text()
i0=interval.index('theorem interval_propagate_candidate')
i1=interval.index('\nend DiophantineConsistency.WangRowsRound3',i0)
new_i=interval[i0:i1].strip().replace('interval_propagate_candidate','interval_propagate')
pulse=(base/'BondPulseCandidate.lean').read_text()
p0=pulse.index('def bondSignal')
p1=pulse.index('\nend DiophantineConsistency.WangRowsRound3',p0)
new_p=pulse[p0:p1].strip().replace('stepTile_edges_candidate','stepTile_edges').replace('stepTile_horizontal_candidate','stepTile_horizontal').replace('stepTile_west_pulse','stepTile_west').replace('stepTile_east_pulse','stepTile_east')
metrics=[]
for name,start,end,repl,api in [
 ('WangTiles942ResetRows.lean','theorem interval_propagate (','/-- A reset\'s east1',new_i,'exact signature preserved'),
 ('WangTiles942StepConstruction.lean','/-- The only west signal','/-- The constructed row',new_p,'stepTile_west/east normalize to bondSignal; all other public theorem statements unchanged')]:
 old=(src/name).read_text();s=old.index(start);e=old.index(end,s)
 # Reset interval retains preceding documentation; StepConstruction comments counted honestly.
 new=old[:s]+repl+'\n\n'+old[e:]
 (out/name).write_text(new)
 (base/(name+'.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name,tofile='b/Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name)))
 oldscope=old[s:e].strip();newscope=repl.strip()
 # Strip block comments for nonblank source counts (no nested comments in scopes).
 code=lambda t: '\n'.join(x for x in re.sub(r'/\-.*?\-/','',t,flags=re.S).splitlines() if x.strip())
 metrics.append({'module':name,'old_span_start_line':old[:s].count('\n')+1,'old_span_end_line':old[:e].count('\n'),
 'old_span_lines':len(oldscope.splitlines()),'new_span_lines':len(newscope.splitlines()),
 'old_span_nonblank_code_lines':len(code(oldscope).splitlines()),'new_span_nonblank_code_lines':len(code(newscope).splitlines()),
 'old_span_utf8_bytes':len(oldscope.encode()),'new_span_utf8_bytes':len(newscope.encode()),
 'api':api,'validation':'uncompiled proposal; textual diff only','source_sha256':hashlib.sha256(old.encode()).hexdigest()})
(base/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
