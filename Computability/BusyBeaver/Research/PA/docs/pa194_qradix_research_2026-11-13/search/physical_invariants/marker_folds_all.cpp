#include <array>
#include <map>
#include <vector>
#include <set>
#include <fstream>
#include <sstream>
#include <iostream>
#include <chrono>
using namespace std;
struct Act{int w,d,n;};
struct Test{int tape,head,targetTape,targetHead,targetState;};
int main(int argc,char**argv){
 if(argc<3)return 2;const int K=5,LIMIT=300;
 Act rows[2500][2];bool exists[2500]={};vector<int>states;string line;
 ifstream tf(argv[1]);int q,b,w,n;char d;
 while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);s>>q>>b>>w>>d>>n;
  rows[q][b]={w,d=='R'?1:-1,n};if(!exists[q])states.push_back(q);exists[q]=true;}
 map<int,vector<int>>pats;ifstream pf(argv[2]);int p;while(pf>>q>>p)pats[q].push_back(p);
 vector<Act>actions;for(int q:states)for(int w:{0,1})for(int d:{-1,1})actions.push_back({w,d,q});
 long long trials=0,pairs=0;int hits=0;auto started=chrono::steady_clock::now();
 for(size_t ia=0;ia<states.size();ia++)for(size_t ib=ia+1;ib<states.size();ib++){
  int a=states[ia],b=states[ib];if(a==74||b==74)continue;
  bool bad=false;for(int q:{a,b})for(int bit:{0,1})if(rows[q][bit].n==a||rows[q][bit].n==b)bad=true;
  if(bad)continue;vector<pair<int,int>>incoming;bool avoid[2500][2]={};
  for(int q:states)for(int bit:{0,1})if(rows[q][bit].n==a||rows[q][bit].n==b){incoming.push_back({q,bit});avoid[q][bit]=true;}
  if(incoming.empty())continue;pairs++;
  for(int polarity:{0,1}){
   array<vector<Test>,2>tests;
   for(auto[q,bit]:incoming){Act old=rows[q][bit];int mark=(old.n==b)^polarity;
    for(int pat:pats[q]){if((pat>>K&1)!=bit)continue;
     int tape=(pat&~(1<<K))|(old.w<<K),head=old.d,read=tape>>(head+K)&1;Act second=rows[old.n][read];
     int target=(tape&~(1<<(head+K)))|(second.w<<(head+K));
     tests[read].push_back({(pat&~(1<<K))|(mark<<K),head,target,head+second.d,second.n});
    }
   }
   array<vector<Act>,2>choices;
   for(int bit:{0,1}){
    for(auto first:actions){if(first.n==a||first.n==b)continue;trials++;bool good=true;
     for(auto test:tests[bit]){int tape=(test.tape&~(1<<(test.head+K)))|(first.w<<(test.head+K)),head=test.head+first.d,c=first.n;bool hit=false;
      for(int step=2;step<=LIMIT;step++){
       if(c==test.targetState&&head==test.targetHead&&tape==test.targetTape){hit=true;break;}
       if(head < -K||head>K||c<0||c>=2500||!exists[c]||c==a||c==b)break;
       int read=tape>>(head+K)&1;if(avoid[c][read])break;
       Act next=rows[c][read];tape=(tape&~(1<<(head+K)))|(next.w<<(head+K));head+=next.d;c=next.n;
      }
      if(!hit){good=false;break;}
     }
     if(good)choices[bit].push_back(first);
    }
    if(choices[bit].empty())break;
   }
   if(!choices[0].empty()&&!choices[1].empty()){
    cout<<"{\"remove\":"<<a<<",\"keep\":"<<b<<",\"polarity\":"<<polarity<<",\"choices\":[";
    for(int bit:{0,1}){if(bit)cout<<',';cout<<'[';bool sep=false;for(auto ac:choices[bit]){if(sep)cout<<',';sep=true;cout<<'['<<ac.w<<','<<ac.d<<','<<ac.n<<']';}cout<<']';}cout<<"]}"<<endl;hits++;
   }
  }
 }
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 cerr<<"{\"independent_pairs\":"<<pairs<<",\"action_trials\":"<<trials<<",\"hits\":"<<hits<<",\"seconds\":"<<seconds<<"}"<<endl;
}
