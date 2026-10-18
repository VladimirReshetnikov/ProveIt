"""Own guard source adaptation only; no generator, guard or proof invocation."""
from pathlib import Path
import ast,difflib,hashlib,json
B=Path(__file__).resolve().parent;old=B.parent/'v3/check-production-v3.py';text=old.read_text();before=text
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(old)=='8b86edb49eb4bf9e8f82e6e5f10d012671a804bb4bd8743ab55d710bf3082ec5'
g=B/'generate_sites_routing245_v4.py';ast.parse(g.read_text())
changes=[
 ('Pins the complete209-unit refined source manifest. Direct imports select exact\nalready successful parents; three measured pilots and thirteen original successful\nbatch modules and passed cut43 are reused without proof replay. Both failures are retained.',
  'Pins the complete599-unit cap32-refined source manifest. Direct imports select exact\nalready successful parents; three pilots, thirteen original batches, passed cut43,\nand eight v3 successes are reused without proof replay. All three failures remain.'),
 ("MANIFEST_SHA='ca70be3402b6a0b1c33708970ac6400bcba7843382dd43e77fe09c9523e7db6b'",'MANIFEST_SHA=None  # Pin only after root emits and reviews the v4 manifest.'),
 ("GENERATOR_SHA='2c385ee00333bc4dec8a3b257ff7042de309368140f8b8eb536a6bce06e82f21'",'GENERATOR_SHA='+repr(sha(g))),
 ('# All418 generated source/audit files remain bound','# All1198 generated source/audit files remain bound'),
 ("default=Path('/tmp/zfc-routing245-lean/coverage-production/v3/sources/generation.json')","default=HERE/'sources/generation.json'"),
 ("default=HERE/'generate_sites_routing245_v3.py'","default=HERE/'generate_sites_routing245_v4.py'"),
 ('len(set(modules))==209','len(set(modules))==599'),
 ('(431,431,476,479)','(905,905,958,961)'),
 ("plan['leaves']==6460 and plan['guard_cases']==8391 and plan['decoder_depth']==51 and", "plan['leaves']==6460 and plan['guard_cases']==8391 and plan['decoder_depth']==51 and\n      plan['max_guards_per_new_closed_proof']==32 and plan['effective_frontier_cuts']==478 and plan['effective_binary_joins']==477 and"),
 ('args.start+args.count<=209','args.start+args.count<=599'),
 ('len(available)==17','len(available)==25'),
 ("sum(u['origin']=='v2_single_cut' and u['cuts']==[43] for u in plan['reused_units'])==1 and\n      sum(u['probes'] for u in plan['reused_units'])==45 and sum(u['callers'] for u in plan['reused_units'])==48,", "sum(u['origin']=='v2_single_cut' and u['cuts']==[43] for u in plan['reused_units'])==1 and\n      sorted(u['original_unit_index'] for u in plan['reused_units'] if u['origin']=='v3_production')==list(range(8)) and\n      sum(u['probes'] for u in plan['reused_units'])==53 and sum(u['callers'] for u in plan['reused_units'])==56,"),
 ("'Require exact three pilots, thirteen passed original batches, and passed cut43.'", "'Require exact three pilots, thirteen original batches, passed cut43, and eight v3 successes.'"),
 ('0<=i<209','0<=i<599'),
 ("v2_cut_reuse=[u['record'] for u in plan['reused_units'] if u['origin']=='v2_single_cut'],", "v2_cut_reuse=[u['record'] for u in plan['reused_units'] if u['origin']=='v2_single_cut'],\n            v3_unit_reuse=[u['record'] for u in plan['reused_units'] if u['origin']=='v3_production'],"),
 ('all209 actual refined units plus three actual pilots, thirteen actual original batches, and actual passed cut43', 'all599 actual cap32-refined units plus three actual pilots, thirteen actual original batches, actual passed cut43, and eight actual v3 units'),
 ('complete_generated_units=209','complete_generated_units=599'),
 ('reused_v2_cut_units=1,','reused_v2_cut_units=1,reused_v3_units=8,'),
 ('complete_probes=476,complete_callers=479','complete_probes=958,complete_callers=961'),
]
for a,b in changes:
 assert text.count(a)==1,(a,text.count(a));text=text.replace(a,b)
assert text[text.index('def run_unit'):text.index('def unit_descriptor')].replace('All1198','All418')==before[before.index('def run_unit'):before.index('def unit_descriptor')]
assert text[text.index('def unit_descriptor'):text.index('def main():')]==before[before.index('def unit_descriptor'):before.index('def main():')]
ast.parse(text)
t=B/'check-production-v4.template.py';assert not t.exists();t.write_text(text)
(B/'guard-v4.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),text.splitlines(True),fromfile=str(old),tofile=str(t))))
freeze='''#!/usr/bin/env python3
"""Freeze exact v4 manifest pin after root source emission; no proof execution."""
from pathlib import Path
import argparse,ast,hashlib,json
HERE=Path(__file__).resolve().parent
TEMPLATE_SHA=REPLACE_TEMPLATE
GENERATOR_SHA=REPLACE_GENERATOR
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--manifest',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 t=HERE/'check-production-v4.template.py';need(sha(t)==TEMPLATE_SHA,'Template changed.')
 p=a.manifest.resolve();d=json.loads(p.read_text());need(d['status']=='GENERATED_SOURCE_ONLY_UNBUILT','Wrong manifest status.')
 need(d['generator']['sha256']==GENERATOR_SHA==sha(d['generator']['path']),'Generator changed.')
 need((d['generated_units'],d['reused_unit_count'],d['chunks'],d['joins'],d['leaves'],d['guard_cases'],d['decoder_depth'])==(599,25,236,235,6460,8391,51),'Wrong complete census.')
 need((d['generated_probes'],d['generated_callers'],d['complete_probes'],d['complete_callers'])==(905,905,958,961),'Wrong audit census.')
 need(d['max_guards_per_new_closed_proof']==32 and d['effective_frontier_cuts']==478 and d['effective_binary_joins']==477,'Wrong refinement policy.')
 us=d['units'];need(len(us)==599 and len({u['module']for u in us})==599,'Wrong module schedule.')
 need(sum(u['kind']=='closed_refined_part'for u in us)==398 and sum(u['kind']=='refined_cut_composition'for u in us)==157 and sum(u['kind']=='closed_cuts'for u in us)==28,'Wrong proof partition.')
 for u in us:
  for role in ('source','audit'):need(sha(p.parent/u[role])==u[role+'_sha256'],'Changed generated bytes.')
  if u['kind']in('closed_cuts','closed_refined_part'):need(u['guards']<=32,'Unrefined large closed proof.')
 need(len(d['refinements'])==157 and sum(len(q['parts'])for q in d['refinements'])==398 and sum(len(q['joins'])for q in d['refinements'])==241,'Wrong local structural joins.')
 text=t.read_text();mark='MANIFEST_SHA=None  # Pin only after root emits and reviews the v4 manifest.'
 need(text.count(mark)==1,'Manifest placeholder differs.');text=text.replace(mark,'MANIFEST_SHA='+repr(sha(p)))
 mark="default=HERE/'sources/generation.json'";need(text.count(mark)==1,'Default differs.');text=text.replace(mark,'default=Path('+repr(str(p))+')')
 ast.parse(text);out=a.output.resolve();need(out.parent==HERE and not out.exists(),'Use a new guard beside the frozen template.');out.write_text(text)
 print(json.dumps({'status':'SOURCE_ONLY_GUARD_FROZEN_UNEXECUTED','manifest':{'path':str(p),'sha256':sha(p)},'guard':{'path':str(out),'sha256':sha(out)}},indent=2))
if __name__=='__main__':main()
'''.replace('REPLACE_TEMPLATE',repr(sha(t))).replace('REPLACE_GENERATOR',repr(sha(g)))
ast.parse(freeze);f=B/'freeze_guard_v4.py';assert not f.exists();f.write_text(freeze)
print(json.dumps({p.name:sha(p)for p in[g,t,f,B/'guard-v4.diff']},indent=2))
