#!/usr/bin/env python3
"""Compare new complete binary tables against every recognized pinned 194-control table.

The graph comparator allows every spanning choice of start and arbitrary state
renaming. It additionally allows global reflection and erases final halt actions.
An optional symbol-complement check is stronger structural comparison only: symbol
exchange alone does not preserve an all-zero blank convention. A nonmatching hash
is conclusive inequality of the underlying canonical tuples (no hash injectivity
assumption is used for that direction). Matching hashes are reported conservatively.
"""
import argparse,hashlib,importlib.util,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('audit',HERE/'audit_corpus.py');au=importlib.util.module_from_spec(sp);sp.loader.exec_module(au)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--census',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);ap.add_argument('--start',type=int,default=0);ap.add_argument('tables',nargs='+',type=pathlib.Path);a=ap.parse_args()
 raw=a.census.read_bytes();j=json.loads(raw);front=[c for c in j['classes'] if c['states']==194];out=[];seen={}
 for p in a.tables:
  b=p.read_bytes();d=au.parse_text(b);assert d and len(d[1])==194 and a.start in d[1],p
  canon,n=au.canonical(d,a.start);assert n==194,(p,n)
  info=au.classify(d)
  rows,states,halt=d
  comp=({(q,1-r):(1-w,move,t) for (q,r),(w,move,t) in rows.items()},states,halt)
  compinfo=au.classify(comp)
  keys={info['halting_graph_sha256'],compinfo['halting_graph_sha256']}
  matches=[c['action_graph_sha256'] for c in front if c['halting_graph_sha256'] in keys]
  othermatches=[name for name,keyset in seen.items() if keys&keyset]
  row={'path':str(p),'sha256':au.sha(b),'normalized_sha256':au.sha(au.normalized(d)),'states':194,'rows':388,'start':a.start,'all_states_graph_reachable':True,'halt':halt,'rooted_action_sha256':au.canonhash(canon),'action_graph_sha256':info['action_graph_sha256'],'cosmetic_comparison_keys':sorted(keys),'matching_prior_action_graphs':matches,'matching_other_candidates':othermatches,'new_within_recognized_corpus':not matches and not othermatches}
  out.append(row);seen[str(p)]=keys
 result={'scope':__doc__,'census_sha256':au.sha(raw),'prior_spanning194_classes':len(front),'nonspanning194_normalized_tables':sum(v['states']==194 and not v['spanning_roots'] for v in j['identities'].values()),'results':out}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
