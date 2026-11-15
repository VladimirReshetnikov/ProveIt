#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

struct Action { int write,dir; long long target; };
int main(int argc,char**argv){
 if(argc<2)return 2;
 const int limit=100000;
 std::cout<<"table,start,status,steps,state,head,ones,leftmost,rightmost,write,move,next\n";
 for(int fi=1;fi<argc;++fi){
  std::ifstream f(argv[fi]);if(!f)return 3;
  std::map<long long,std::array<Action,2>> rows;std::set<std::pair<long long,int>> keys;
  std::string line;
  while(std::getline(f,line)){
   if(line.empty()||line[0]=='#')continue;
   std::istringstream s(line);long long q,n;int b,w;char d;
   if(!(s>>q>>b>>w>>d>>n))continue;
   if(b<0||b>1||w<0||w>1||(d!='L'&&d!='R')||!keys.insert({q,b}).second)return 4;
   rows[q][b]={w,d=='R'?1:-1,n};
  }
  if(rows.size()!=193||keys.size()!=386)return 5;
  for(const auto& item:rows){
   long long start=item.first,q=start,h=0;std::set<long long> ones;std::string status;int t;
   Action a{0,0,-1};
   for(t=0;t<=limit;++t){
    auto it=rows.find(q);
    if(it==rows.end()){status="HALT";break;}
    if(t==limit){status="LIMIT";break;}
    int b=ones.count(h)?1:0;a=it->second[b];
    bool blank_ray=ones.empty()||(a.dir>0?h>*ones.rbegin():h<*ones.begin());
    if(b==0&&a.target==q&&blank_ray){status="RAY";break;}
    if(a.write)ones.insert(h);else ones.erase(h);
    q=a.target;h+=a.dir;
   }
   std::cout<<argv[fi]<<','<<start<<','<<status<<','<<t<<','<<q<<','<<h<<','<<ones.size()<<',';
   if(!ones.empty())std::cout<<*ones.begin();std::cout<<',';
   if(!ones.empty())std::cout<<*ones.rbegin();std::cout<<','<<a.write<<','<<a.dir<<','<<a.target<<'\n';
  }
 }
}
