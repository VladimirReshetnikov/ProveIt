// Search three-row local repairs, with necessary failure-trace branching.
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
using namespace std;
struct Row{int w,d,target;};
struct Patch{int key; Row row;};
int N,drop,keep;Row table[256][2];vector<int> ctx[256][2];
long long calls[4]={}, tested[4]={}, found=0;ofstream out;
inline int project(int q){return q==drop?keep:q;}
bool run(int q,int b,int mask,const vector<Patch>& patches,bitset<512>* visited){
 Row orig=table[q][b];int target=project(orig.target),th=orig.d,tt=(mask&~4)|(orig.w<<2);
 int state=project(q),head=0,tape=mask;
 for(int i=0;i<16;i++){
  if(state>=N||head< -2||head>2)return false;
  int bit=(tape>>(head+2))&1,key=2*state+bit;
  if(visited)visited->set(key);
  Row r=table[state][bit];for(auto p:patches)if(p.key==key){r=p.row;break;}
  tape=(tape&~(1<<(head+2)))|(r.w<<(head+2));head+=r.d;state=project(r.target);
  if(state==target&&head==th&&tape==tt)return true;
 }
 return false;
}
bool scan(vector<Patch>& patches,int remaining){
 calls[remaining]++;
 bitset<512> candidates,minimum;size_t least=513;bool failure=false;
 candidates.set();vector<int> states={drop,keep};for(auto p:patches)states.push_back(p.key/2);
 sort(states.begin(),states.end());states.erase(unique(states.begin(),states.end()),states.end());
 for(int q:states)for(int b=0;b<2;b++)for(int mask:ctx[q][b]){
  bitset<512> visited;
  if(!run(q,b,mask,patches,remaining?&visited:nullptr)){
   failure=true;if(!remaining)return false;
   visited[2*drop]=visited[2*drop+1]=false;
   for(auto p:patches)visited[p.key]=false;
   if(visited.none())return false;
   if(remaining==1){candidates&=visited;if(candidates.none())return false;}
   else if(visited.count()<least){minimum=visited;least=visited.count();}
  }
 }
 if(!failure){found++;out<<"PASS "<<drop<<" "<<keep;for(auto p:patches)out<<" "<<p.key<<" "<<p.row.w<<" "<<p.row.d<<" "<<p.row.target;out<<endl;return true;}
 if(remaining>1)candidates=minimum;
 for(int key=0;key<2*N;key++)if(candidates[key]){
  patches.push_back({key,{}});
  for(int dest=0;dest<=N;dest++)if(dest!=drop)for(int w=0;w<2;w++)for(int d:{-1,1}){
   if(table[key/2][key%2].w==w&&table[key/2][key%2].d==d&&project(table[key/2][key%2].target)==dest)continue;
   patches.back().row={w,d,dest};tested[remaining]++;
   scan(patches,remaining-1);
  }
  patches.pop_back();
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=7)return 2;N=stoi(argv[4]);drop=stoi(argv[5]);keep=stoi(argv[6]);
 ifstream tf(argv[1]),cf(argv[2]);out.open(argv[3]);int q,b,w,t,mask;string d;
 while(tf>>q>>b>>w>>d>>t)table[q][b]={w,d=="R"?1:-1,t};
 while(cf>>q>>b>>mask)ctx[q][b].push_back(mask);
 vector<Patch> p;scan(p,3);
 cout<<"drop "<<drop<<" keep "<<keep<<" found "<<found;for(int i=0;i<4;i++)cout<<" calls"<<i<<" "<<calls[i]<<" tested"<<i<<" "<<tested[i];cout<<endl;
}
