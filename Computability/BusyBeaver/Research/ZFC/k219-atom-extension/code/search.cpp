#include <bits/stdc++.h>
using namespace std;
struct Node {vector<short> s;int a,b,cost;};
struct Hash{size_t operator()(vector<short>const&v)const{size_t h=1469598103934665603ull;for(short x:v)h=(h^(x+2))*1099511628211ull;return h;}};
int main(int argc,char**argv){if(argc!=4){cerr<<"usage: search atoms output rootcost"<<endl;return 64;}int rootcost=atoi(argv[3]);if(rootcost!=4&&rootcost!=5)return 64;ifstream in(argv[1]);int M,na;in>>M>>na;if(!in||M!=9||na!=19)return 65;int W=M+1,N=W*W;vector<Node>g;g.reserve(800000);unordered_map<vector<short>,int,Hash>index;vector<vector<int>>layers(16);ofstream out(argv[2]);
for(int a=0;a<na;a++){Node n;n.a=n.b=-1;n.cost=0;n.s.resize(N);for(auto&x:n.s){in>>x;if(!in||x < -1||x>=N*16)return 65;}int id=g.size();g.push_back(n);if(!index.count(n.s)){index[n.s]=id;layers[0].push_back(id);}}
auto started=chrono::steady_clock::now(); long long trials=0;int hits=0;int maxcost=rootcost;
for(int c=1;c<=maxcost;c++){
 for(int ca=0;ca<c;ca++){int cb=c-1-ca;
 for(int a:layers[ca])for(int b:layers[cb]){trials++;if(chrono::duration<double>(chrono::steady_clock::now()-started).count()>109){cout<<"WALL_LIMIT trials "<<trials<<" hits "<<hits<<endl;return 2;}Node n;n.a=a;n.b=b;n.cost=c;n.s.resize(N);
 bool goalOnly=(c==maxcost), badGoal=false;
 vector<int> vs;if(goalOnly){for(int x=0;x<5;x++)for(int y=0;y<5;y++)vs.push_back(x*W+y);}else{for(int v=0;v<N;v++)vs.push_back(v);}
 for(int v:vs){int cur=v,step=0,e=-1;unsigned char seen[121]={};
 while(step++<N+2){if(seen[cur]){e=-1;break;}seen[cur]=1;e=g[a].s[cur];if(e<0)break;int k=e%16,st=e/16;
 if(k){if(k<8)e--;break;}
 e=g[b].s[st];if(e<0)break;k=e%16;st=e/16;
 if(k==9){cur=st;continue;}if(k>9)e--;break;
 }
 n.s[v]=e;
 if(goalOnly && e!=((v/W)==(v%W)?0:1)){badGoal=true;break;}
 }
 if(badGoal)continue;
 if(goalOnly){hits++;out<<"H "<<a<<" "<<b<<" "<<c<<"\n";cout<<"HIT_ROOT "<<a<<" "<<b<<" cost "<<c<<" trials "<<trials<<endl;continue;}
 if(index.count(n.s))continue;
 if(g.size()>=800000){cout<<"CAP nodes "<<g.size()<<" trials "<<trials<<" hits "<<hits<<endl;return 3;}
 int id=g.size();g.push_back(n);index[n.s]=id;layers[c].push_back(id);out<<id<<" "<<a<<" "<<b<<" "<<c<<"\n";
 bool good=true;for(int x=0;x<5&&good;x++)for(int y=0;y<5;y++)if(n.s[x*W+y]!=(x==y?0:1)){good=false;break;}
 if(good){hits++;cout<<"HIT "<<id<<" cost "<<c<<" trials "<<trials<<endl;}
 }}cout<<"COST "<<c<<" unique "<<layers[c].size()<<" all "<<g.size()<<" trials "<<trials<<" hits "<<hits<<endl;
}cout<<"DONE "<<trials<<" hits "<<hits<<endl;}
