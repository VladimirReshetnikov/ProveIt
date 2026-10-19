#!/usr/bin/env python3
"""Portable, bounded search for locally certified binary Turing-machine folds.

Requires Python 3.9+ and a C++17 compiler (default: c++). No third-party Python
packages or repository imports are used. Compilation is confined to a temporary
directory. See --help and fold_search.tex for the exact search class.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

ENGINE = r'''
#include <algorithm>
#include <bitset>
#include <fstream>
#include <iostream>
#include <queue>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Edge { int w,d,t; };
struct Domain { int edge; bitset<256> support; int duration; };
struct Goal { int q,h,tape,steps; };
Edge tab[256][2]; bool have[256];

int main(int argc,char**argv) {
 try {
  if(argc!=8)throw runtime_error("bad engine arguments");
  string mode=argv[1]; int start=stoi(argv[3]),halt=stoi(argv[4]);
  int K=stoi(argv[5]),fuel=stoi(argv[6]);string prefix=argv[7];
  ifstream input(argv[2]);if(!input)throw runtime_error("cannot open table");
  string line;
  while(getline(input,line)) {
   if(line.empty()||line[0]=='#')continue;
   int q,b,w,t;char d;istringstream row(line);row>>q>>b>>w>>d>>t;
   tab[q][b]={w,d=='R'?1:-1,t};have[q]=true;
  }
  vector<int> states;
  for(int q=0;q<256;q++)if(have[q])states.push_back(q);
  int N=1<<(2*K+1),MASK=N-1;
  vector<vector<bool>> seen(256,vector<bool>(N,false));
  queue<pair<int,int>> work;
  for(int m=0;m<N;m++){seen[start][m]=true;work.push({start,m});}
  long long total=0;
  while(!work.empty()) {
   auto[q,m]=work.front();work.pop();total++;
   if(!have[q])continue;
   auto e=tab[q][(m>>K)&1];int v=(m&~(1<<K))|(e.w<<K);
   v=e.d==1?v>>1:(v<<1)&MASK;
   int add=e.d==1?1<<(2*K):1;
   for(int x:{v,v|add})if(!seen[e.t][x]) {
    seen[e.t][x]=true;work.push({e.t,x});
   }
  }
  vector<vector<int>> masks[256];
  for(int q:states) {
   masks[q].resize(2);
   for(int m=0;m<N;m++)if(seen[q][m])masks[q][(m>>K)&1].push_back(m);
  }
  ofstream inv(prefix+".invariant.txt");
  for(int q:states) {
   inv<<q<<":";
   for(int off=-K;off<=K;off++) {
    int v=-1;
    for(int m=0;m<N;m++)if(seen[q][m]) {
     int b=(m>>(off+K))&1;
     if(v<0)v=b;else if(v!=b){v=2;break;}
    }
    if(v>=0&&v<2)inv<<" "<<off<<"="<<v;
   }
   inv<<" count "<<masks[q][0].size()+masks[q][1].size()<<"\n";
  }
  vector<int> targets=states;targets.push_back(halt);
  vector<Edge> edges;
  for(int w=0;w<=1;w++)for(int d:{-1,1})for(int t:targets)
   edges.push_back({w,d,t});
  vector<Domain> domains[256][2];long long runs=0,domain_count=0;
  for(int q:states)for(int b=0;b<=1;b++) {
   auto target=tab[q][b];int dead=target.t;
   for(int ix=0;ix<(int)edges.size();ix++) {
    Edge e=edges[ix];if(mode=="delete"&&e.t==dead)continue;
    bitset<256> support;int duration=0;bool ok=true;
    for(int m:masks[q][b]) {
     runs++;
     vector<Goal> goals;
     if(mode=="pair") {
      goals.push_back({target.t,target.d,(m&~(1<<K))|(target.w<<K),1});
     } else {
      int oh=0,oq=q,otape=m;
      for(int oldstep=1;oldstep<=fuel;oldstep++) {
       if(oh< -K||oh>K||!have[oq])break;
       auto oe=tab[oq][(otape>>(oh+K))&1];
       otape=(otape&~(1<<(oh+K)))|(oe.w<<(oh+K));
       oh+=oe.d;oq=oe.t;
       goals.push_back({oq,oh,otape,oldstep});
      }
     }
     int tape=(m&~(1<<K))|(e.w<<K),h=e.d,cur=e.t,step=1;
     for(;;) {
      bool matched=false;
      for(auto g:goals)if((mode!="delete"||g.q!=dead)&&
                         h==g.h&&cur==g.q&&tape==g.tape) {
       duration=max(duration,max(step,g.steps));matched=true;break;
      }
      if(matched)break;
      if(step>=fuel||h< -K||h>K||!have[cur]){ok=false;break;}
      int bit=(tape>>(h+K))&1;
      if(mode=="delete" ? (cur==dead||tab[cur][bit].t==dead) : cur==q) {
       ok=false;break;
      }
      support[cur]=true;
      auto next=tab[cur][bit];
      tape=(tape&~(1<<(h+K)))|(next.w<<(h+K));
      h+=next.d;cur=next.t;step++;
     }
     if(!ok)break;
    }
    if(ok){domains[q][b].push_back({ix,support,duration});domain_count++;}
   }
  }
  ofstream dom(prefix+".domains.txt");
  for(int q:states)for(int b=0;b<=1;b++)for(auto item:domains[q][b]) {
   auto e=edges[item.edge];
   dom<<q<<" "<<b<<" "<<e.w<<" "<<e.d<<" "<<e.t<<" "<<item.duration<<" :";
   for(int u:states)if(item.support[u])dom<<" "<<u;
   dom<<"\n";
  }
  int hits=0;
  if(mode=="delete") {
   for(int dead:states)if(dead!=start) {
    vector<pair<int,int>> incoming;
    for(int q:states)for(int b=0;b<=1;b++)if(q!=dead&&tab[q][b].t==dead)
     incoming.push_back({q,b});
    bool ok=true;
    for(auto[q,b]:incoming)if(domains[q][b].empty()){ok=false;break;}
    if(ok) {
     hits++;cout<<"DELETE "<<dead<<"\n";
     for(auto[q,b]:incoming) {
      cout<<q<<"/"<<b<<":";
      for(auto item:domains[q][b]) {
       auto e=edges[item.edge];
       cout<<" ["<<e.w<<","<<e.d<<","<<e.t<<";"<<item.duration<<"]";
      }
      cout<<"\n";
     }
    }
   }
  } else {
   for(int q:states)for(int r:states)if(q<r) {
    vector<int> shared[2];
    for(int b=0;b<=1;b++)for(auto a:domains[q][b])for(auto c:domains[r][b])
     if(a.edge==c.edge&&!a.support[q]&&!a.support[r]&&
        !c.support[q]&&!c.support[r])shared[b].push_back(a.edge);
    for(int a:shared[0])for(int c:shared[1]) {
     hits++;auto x=edges[a],y=edges[c];
     cout<<"MERGE "<<q<<" "<<r<<" : "<<x.w<<" "<<x.d<<" "<<x.t
         <<" ; "<<y.w<<" "<<y.d<<" "<<y.t<<"\n";
    }
   }
  }
  cerr<<"{\"abstract_configurations\":"<<total<<",\"edges_per_row\":"<<edges.size()
      <<",\"window_cases_executed\":"<<runs<<",\"accepted_row_domains\":"<<domain_count
      <<",\"hits\":"<<hits<<"}\n";
  return 0;
 }catch(const exception&e){cerr<<e.what()<<endl;return 1;}
}
'''


def read_table(path, start, halt):
    rows = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 5:
            raise ValueError(f"line {number}: expected q b w L/R target")
        q, b, w, d, target = fields
        q, b, w, target = map(int, (q, b, w, target))
        if not (0 <= q < 256 and 0 <= target < 256 and b in (0, 1)
                and w in (0, 1) and d in ("L", "R")):
            raise ValueError(f"line {number}: invalid row")
        if (q, b) in rows:
            raise ValueError(f"line {number}: duplicate row")
        rows[q, b] = (w, d, target)
    states = sorted({q for q, b in rows})
    if start not in states or halt in states:
        raise ValueError("start must have rows; halt must have no rows")
    if len(rows) != 2 * len(states):
        raise ValueError("each working state needs both rows")
    if any(target not in states and target != halt for w, d, target in rows.values()):
        raise ValueError("every target must be a working state or the declared halt")
    return states


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, help="five-column inherited-label TM table")
    parser.add_argument("--mode", choices=("pair", "block", "delete", "all"), default="pair")
    parser.add_argument("--radius", type=int, default=7, help="window [-K,K], default7")
    parser.add_argument("--fuel", type=int, default=63, help="maximum positive block length")
    parser.add_argument("--start", type=int, default=95)
    parser.add_argument("--halt", type=int, default=254)
    parser.add_argument("--output", type=Path, required=True, help="new results directory")
    parser.add_argument("--compiler", default="c++")
    args = parser.parse_args()
    if not 0 <= args.radius <= 10 or not 1 <= args.fuel <= 10000:
        parser.error("radius must be in0..10 and fuel in1..10000")
    table = args.table.resolve()
    states = read_table(table, args.start, args.halt)
    compiler = shutil.which(args.compiler)
    if compiler is None:
        parser.error("a C++17 compiler is required (use --compiler)")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    metadata = {
        "scope": "Exhaustive enumeration only within the declared local certificate class",
        "initial_tapes": "All binary tapes, at the declared start state",
        "table": str(table),
        "table_sha256": hashlib.sha256(table.read_bytes()).hexdigest(),
        "working_states": len(states), "start": args.start, "halt": args.halt,
        "radius": args.radius, "window_cells": 2 * args.radius + 1,
        "fuel": args.fuel, "compiler": compiler,
        "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "results": {},
    }
    modes = ("pair", "block", "delete") if args.mode == "all" else (args.mode,)
    with tempfile.TemporaryDirectory(prefix="bb-fold-search-") as temporary:
        temporary = Path(temporary)
        source = temporary / "engine.cpp"
        binary = temporary / "engine"
        source.write_text(ENGINE)
        subprocess.run([compiler, "-O3", "-std=c++17", str(source), "-o", str(binary)],
                       check=True, capture_output=True, text=True)
        for mode in modes:
            started = time.monotonic()
            result = subprocess.run(
                [str(binary), mode, str(table), str(args.start), str(args.halt),
                 str(args.radius), str(args.fuel), str(output / mode)],
                check=True, capture_output=True, text=True)
            (output / f"{mode}.hits.txt").write_text(result.stdout)
            record = json.loads(result.stderr)
            record["seconds"] = time.monotonic() - started
            metadata["results"][mode] = record
            (output / "summary.json").write_text(json.dumps(metadata, indent=2) + "\n")
            print(json.dumps({"mode": mode, **record}), flush=True)
    (output / "summary.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
