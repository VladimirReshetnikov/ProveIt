// Research diagnostics, 18 October 2026. See README.md for exact finite scopes.
// Bitset replay derived from attributed ProveIt resource_merge_search.cpp.
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
struct Row{int w,d,t;};using Table=std::array<std::array<Row,2>,256>;
int main(int argc,char**argv){
 std::ifstream in(argv[1]);Table t{};std::vector<int>states;std::string line;
 while(std::getline(in,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,target;char d;std::sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&target);t[q][b]={w,d=='R'?1:-1,target};if(b==0)states.push_back(q);}
 constexpr int limit=2000000;std::ofstream out(argv[2]);
 int pass=0,escape=0,halts=0,bounded=0;
 for(int start:states){int q=start,h=0;std::set<int>ones;bool done=false;
  for(int tick=0;tick<=limit;tick++){
   if(q==254){out<<start<<" HALT "<<tick<<"\n";halts++;done=true;break;}
   int b=ones.count(h);auto row=t[q][b];
   if(b==0&&row.t==q&&(ones.empty()||(row.d==1?h>*ones.rbegin():h<*ones.begin()))){out<<start<<" BLANK_ESCAPE "<<tick<<" "<<q<<" "<<h<<" "<<ones.size()<<"\n";escape++;done=true;break;}
   if(q==96&&!ones.empty()&&*ones.begin()==h-1){
    auto it=ones.lower_bound(h);
    if(it!=ones.end()&&*it-h>=64){
     int header=*it,p=header+1,maximum=*ones.rbegin();std::vector<int>vals;bool ok=true;
     while(p<=maximum){if(ones.count(p)||!ones.count(p+1)){ok=false;break;}int begin=++p;while(ones.count(p))p++;vals.push_back(p-begin-1);}
     if(ok&&vals.size()>=10&&vals[2]==0&&vals[0]==0&&vals[7]==0){out<<start<<" FRAME "<<tick<<" "<<h<<" "<<header;for(int v:vals)out<<" "<<v;out<<"\n";pass++;done=true;break;}
    }
   }
   if(tick==limit)break;
   if(row.w)ones.insert(h);else ones.erase(h);h+=row.d;q=row.t;
  }
  if(!done){out<<start<<" BOUNDED "<<limit<<" "<<q<<" "<<h<<" "<<ones.size()<<"\n";bounded++;}
 }
 std::cerr<<"FINISH frames "<<pass<<" proven_blank_escape "<<escape<<" halts "<<halts<<" bounded "<<bounded<<"\n";
}
