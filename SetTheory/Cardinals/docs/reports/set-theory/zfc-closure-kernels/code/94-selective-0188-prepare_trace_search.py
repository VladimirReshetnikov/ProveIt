#!/usr/bin/env python3
"""Build a discovery-only trace grammar search from attributed routed245 code.

Semantics certificates are checked separately; this generator does not prove a
machine theorem. The original search source remains untouched.
"""
import argparse
import json
from functools import lru_cache
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--criterion', choices=('disjoint', 'readwrite'), default='disjoint')
parser.add_argument('--reference', type=Path, default=BASE / 'packages/zfc245-proof-20261018')
parser.add_argument('--output-directory', type=Path, default=Path(__file__).resolve().parent)
args = parser.parse_args()
REF = args.reference.resolve()
OUT = args.output_directory.resolve()
OUT.mkdir(parents=True, exist_ok=True)
data = json.loads((REF / 'inputs/closed-sequence-grammar-next22.json').read_text())
symbols = json.loads((REF / 'inputs/semantic-symbols.json').read_text())

@lru_cache(None)
def leaves(q):
    row = data['ast_dag'][q]
    return (tuple(row[1]),) if row[0] == 'L' else leaves(row[1]) + leaves(row[2])

footprints = {}
readsets = {}
increments = set()
halt_free = set()
for ch, name in symbols.items():
    atom = data['atoms'][name]
    assert atom['bounds'] == [0, 0]
    ops = leaves(atom['ast'])
    footprints[ch] = {x[1] for x in ops if x[0] in ('inc', 'dec')}
    readsets[ch] = {x[1] for x in ops if x[0] == 'dec'}
    if len(ops) == 1 and ops[0][0] == 'inc':
        increments.add(ch)
    if all(x[0] != 'halt' for x in ops):
        halt_free.add(ch)
pairs = [(a,b) for a in sorted(symbols) for b in sorted(symbols)
         if a < b and a in halt_free and b in halt_free
         and ((footprints[a].isdisjoint(footprints[b])
               or a in increments and b in increments) if args.criterion == 'disjoint'
              else readsets[a].isdisjoint(footprints[b]) and readsets[b].isdisjoint(footprints[a]))]
source = (REF / 'code/state_reduction/anneal_routes_zero6.cpp').read_text()
source = source.replace('#include <vector>', '#include <vector>\n#include <queue>\n#include <array>')
marker = 'int intern(const string&s)'
assert source.count(marker) == 1
code = r'''
// New trace-normalization layer: lexicographically least topological ordering.
bool independent_char[128][128] = {};
unordered_map<string,string> normal_cache;
string trace_normal(const string& s) {
 auto old=normal_cache.find(s); if(old!=normal_cache.end()) return old->second;
 int n=s.size(); if(n<2)return s;
 vector<vector<int>> edges(n);vector<int>degree(n,0);array<int,128>last;last.fill(-1);
 for(int i=0;i<n;i++) {
  for(int c=0;c<128;c++) if(last[c]>=0&&!independent_char[(unsigned char)s[i]][c]){
   edges[last[c]].push_back(i);degree[i]++;
  }
  last[(unsigned char)s[i]]=i;
 }
 priority_queue<pair<char,int>,vector<pair<char,int>>,greater<pair<char,int>>> ready;
 for(int i=0;i<n;i++)if(!degree[i])ready.push({s[i],i});
 string ans;ans.reserve(n);
 while(!ready.empty()){
  auto[c,i]=ready.top();ready.pop();ans+=c;
  for(int j:edges[i])if(!--degree[j])ready.push({s[j],j});
 }
 if(ans.size()!=s.size()){cerr<<"trace DAG failure"<<endl;exit(12);}
 normal_cache[s]=ans;return ans;
}
bool cross_commutes(int x,int y){
 for(char a:words[x])for(char b:words[y])if(!independent_char[(unsigned char)a][(unsigned char)b])return false;
 return true;
}
'''
source = source.replace(marker, code + '\nint intern(const string&raw)')
source = source.replace('int intern(const string&raw){', 'int intern(const string&raw){string s=trace_normal(raw);')
init = ''.join("independent_char['%s']['%s']=independent_char['%s']['%s']=true;"%(a,b,b,a) for a,b in pairs)
source = source.replace('int main(int argc,char**argv){', 'int main(int argc,char**argv){'+init)
source = source.replace('ABSTRACT_ROUTING_GRAMMAR_ONLY', 'ABSTRACT_TRACE_GRAMMAR_ONLY')
source = source.replace('else if(move_kind<80)', 'else if(move_kind<78)')
source = source.replace('else if(move_kind<88)changed=route_contexts(next,nextroute,rng,true);',
'''else if(move_kind<84){vector<int>active;for(auto[q,r]:current)active.push_back(q);int q=active[rng()%active.size()];auto r=current.at(q);if(cross_commutes(r.a,r.b)&&permitted(r.b,r.a))next[q]={r.b,r.a};else changed=false;}
 else if(move_kind<90)changed=route_contexts(next,nextroute,rng,true);''')
# The original alternative-cut code searches literal substrings in ids. Its
# proposals remain valid when checked by normalized concatenation. Cache each
# substring's normalized key before looking it up.
source = source.replace('ids.find(w.substr(0,k)),bi=ids.find(w.substr(k))',
                        'ids.find(trace_normal(w.substr(0,k))),bi=ids.find(trace_normal(w.substr(k)))')
(OUT/('anneal_trace_'+args.criterion+'.cpp')).write_text(source)
(OUT/('independence_'+args.criterion+'.json')).write_text(json.dumps({
 'symbols':symbols,'halt_free':sorted(halt_free),'primitive_increments':sorted(increments),
 'footprints':{k:sorted(v)for k,v in footprints.items()},'decrement_registers':{k:sorted(v)for k,v in readsets.items()},
 'independent_pairs':pairs, 'criterion':args.criterion,
 'scope':'Syntactic closed halt-free atoms; explicitly stated independence criterion.'
},indent=2)+'\n')
grammar=json.loads((REF/'grammar.json').read_text())
resume=[str(len(grammar['rules']))]+[str(len(a))+' '+w for w,a,b in grammar['rules']]
resume += [str(len(grammar['routes']))]+[r['word']for r in grammar['routes']]
(OUT/'resume245.txt').write_text('\n'.join(resume)+'\n')
print(json.dumps({'independent_pairs':len(pairs),'halt_free':len(halt_free),'rules':len(grammar['rules'])}))
