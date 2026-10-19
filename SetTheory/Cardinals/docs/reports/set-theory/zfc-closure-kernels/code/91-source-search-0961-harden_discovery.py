#!/usr/bin/env python3
"""Make an annealer reject incomplete proposed grammars instead of aborting.

Historical source files are inputs and are never overwritten. This patch changes
discovery error handling only; every output still requires independent auditing.
"""
import argparse
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source", type=Path)
    p.add_argument("output", type=Path)
    a = p.parse_args()
    assert a.source.resolve() != a.output.resolve()
    s = a.source.read_text()
    start = s.index("void collect(")
    end = s.index("\nbool matches", start)
    s = s[:start] + '''// A malformed trial dictionary is a rejected proposal, not a fatal run.
long long closure_rejections=0;
bool collect(Grammar&g,const vector<int>&route){
 unordered_set<int>seen;vector<int>todo=roots;
 todo.insert(todo.end(),route.begin(),route.end());
 while(!todo.empty()){
  int q=todo.back();todo.pop_back();
  if(terminal(q)||!seen.insert(q).second)continue;
  auto it=g.find(q);
  if(it==g.end())return false;
  todo.push_back(it->second.a);todo.push_back(it->second.b);
 }
 // Erase only after the complete traversal has established closure.
 for(auto it=g.begin();it!=g.end();)
  if(!seen.count(it->first))it=g.erase(it);else++it;
 // Callers must enter a transparent dictionary state, not an atomic key
 // temporarily given a rule by a synthesis proposal and erased above.
 for(int q:route)if(!g.count(q))return false;
 return true;
}
''' + s[end:]
    old = "collect(initial,initialroute);"
    assert s.count(old) == 1
    s = s.replace(old, 'if(!collect(initial,initialroute)){cerr<<"initial grammar closure fails"<<endl;return 2;}')
    old = "collect(next,nextroute);"
    assert s.count(old) == 1
    s = s.replace(old, 'if(!collect(next,nextroute)){closure_rejections++;continue;}')
    old = '<<" restarts "<<restarts<<" sec "<<elapsed<<endl;'
    assert s.count(old) == 1
    s = s.replace(old, '<<" restarts "<<restarts<<" closure_rejections "<<closure_rejections<<" sec "<<elapsed<<endl;')
    if "iteration_limit" not in s:
        old = "int nr,nroot,na;"
        assert s.count(old) == 1
        s = s.replace(old, "long long iteration_limit=argc>9?stoll(argv[9]):0;int nr,nroot,na;")
        old = "count())<seconds){iter++;"
        assert s.count(old) == 1
        s = s.replace(old, "count())<seconds&&(!iteration_limit||iter<iteration_limit)){iter++;")
    a.output.write_text(s)


if __name__ == "__main__":
    main()
