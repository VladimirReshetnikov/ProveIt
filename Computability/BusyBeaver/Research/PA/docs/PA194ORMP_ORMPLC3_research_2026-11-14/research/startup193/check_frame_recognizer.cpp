// Exercises the exact frame() function used by the trace-driven search.
#define main search_program_main
#include "trace_startup.cpp"
#undef main
#include <cassert>
int main(int argc,char**argv){
 if(argc!=2)return 2;
 vector<pair<int,string>> paths;int pc,mask;string p;ifstream in(argv[1]);
 while(in>>pc>>p>>mask){paths.push_back({pc,p});int a=0;for(char c:p){int b=c-'0';if(trie[a].child[b]<0){int z=trie.size();trie[a].child[b]=z;trie.emplace_back();}a=trie[a].child[b];}trie[a].site=pc;}
 hitstream.open("/dev/null");long long valid=0,invalid=0,twelve=0;
 for(auto [pc,path]:paths)for(int kind=0;kind<4;++kind){
  Run s;s.q=84;s.h=kind%2?-37:17;s.start=74;
  auto put=[&](int h){if(!s.tape[h+OFF]){s.tape[h+OFF]=1;++s.ones;if(s.ones==1)s.left=s.right=h;else{s.left=min(s.left,h);s.right=max(s.right,h);}}};
  int span=kind<2?(int)path.size():48;
  put(s.h-1);for(size_t i=0;i<path.size();++i)if(path[i]=='1')put(s.h+i);
  int sep=s.h+span;put(sep);int h=sep;
  int count=kind==3?12:10;
  for(int i=0;i<count;++i){++h;int v=kind==3?i%3:0;for(int j=0;j<=v;++j)put(++h);}
  assert(frame(s));++valid;if(s.ones==12)++twelve;
  // An extra one to the left violates the complete exterior/marker condition.
  Run bad=s;bad.tape[s.h-2+OFF]=1;++bad.ones;bad.left=s.h-2;assert(!frame(bad));++invalid;
  // Delete the mandatory zero separator before the first unary register.
  bad=s;bad.tape[sep+1+OFF]=1;++bad.ones;assert(!frame(bad));++invalid;
 }
 assert(paths.size()==3673 && twelve>0);
 cout<<"{\"source_paths\":"<<paths.size()<<",\"accepted_complete_frames\":"<<valid<<",\"rejected_malformed_frames\":"<<invalid<<",\"accepted_twelve_one_frames\":"<<twelve<<",\"status\":\"PASS\"}\n";
}
