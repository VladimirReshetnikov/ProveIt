// Exhaustive two-arbitrary-row local synthesis over an explicit context list.
// A fold identifies drop with keep, redirects incoming targets, and permits
// at most two remaining rows to change. Positive <=16-step blocks must match
// each parent transition's projected state, head, and all five tape cells.
// This extends the template of ProveIt's PA196 single-helper-row screen.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
constexpr int N=6; constexpr int R=4; constexpr int S=64;
struct Row{int w,d,t;};
Row tab[N][2];vector<int> contexts[N][2]; int offsets[N];
int proj(int q,int drop,int keep){return q==drop?keep:q;}
bool run(int drop,int keep,int orig,int b,int mask,int key1,Row row1,int key2,Row row2,bitset<2*N>* visited=nullptr){
 auto old=tab[orig][b];int goal=(mask&~(1<<R))|(old.w<<R),goalhead=old.d+(old.t==drop?offsets[drop]:0),goalstate=proj(old.t,drop,keep);
 int q=proj(orig,drop,keep),h=orig==drop?offsets[drop]:0,tape=mask;
 for(int j=0;j<S;j++){
  if(q>=N||h< -R||h>R)return false;
  int read=(tape>>(h+R))&1,key=2*q+read;if(visited)visited->set(key);
  Row r=tab[q][read];if(r.t==drop){r.t=keep;r.d=-r.d;}if(key==key1)r=row1;else if(key==key2)r=row2;
  tape=(tape&~(1<<(h+R)))|(r.w<<(h+R));h+=r.d;q=proj(r.t,drop,keep);
  if(q==goalstate&&h==goalhead&&tape==goal)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);int maxdrop=stoi(argv[4]);
 int q,b,w,t,m;string d;int rows=0;
 while(tf>>q>>b>>w>>d>>t){if(q<0||q>=N||b<0||b>1||w<0||w>1||(d!="L"&&d!="R")||t<0||t>N)return 4;tab[q][b]={w,d=="R"?1:-1,t};rows++;}
 if(rows!=2*N)return 5;
 while(cf>>q>>b>>m){if(q<0||q>=N||b<0||b>1||m<0||m>=(1<<(2*R+1))||((m>>R)&1)!=b)return 6;contexts[q][b].push_back(m);}
 long long pairs=0,firstkeys=0,firstrows=0,secondkeys=0,secondrows=0,reps=0,survivors=0,plain=0;
 auto start=chrono::steady_clock::now();
 for(int drop=0;drop<maxdrop;drop++){
  int incoming=0;bool uniform=true;
  for(int q=0;q<N;q++)for(int b=0;b<2;b++)if(tab[q][b].t==drop){int d=tab[q][b].d;if(incoming&&incoming!=d)uniform=false;incoming=d;}
  if(!uniform||!incoming)continue;offsets[drop]=-2*incoming;
  for(int keep=0;keep<N;keep++){
   if(drop==keep)continue;pairs++;
   bitset<2*N> first;bool failure=false;
   for(int orig:{drop,keep}){for(int bit:{0,1}){for(int win:contexts[orig][bit]){
    bitset<2*N> visited;if(!run(drop,keep,orig,bit,win,-1,{},-1,{},&visited)){first=visited;failure=true;break;}
   }if(failure)break;}if(failure)break;}
   if(!failure){plain++;out<<"PLAIN "<<drop<<' '<<keep<<'\n';continue;}
   first.reset(2*drop);first.reset(2*drop+1);
   for(int key1=0;key1<2*N;key1++)if(first[key1]){
    firstkeys++;int helper1=key1/2;
    for(int target1=0;target1<=N;target1++)if(target1!=drop)for(int write1:{0,1})for(int dr1:{-1,1}){
     firstrows++;Row row1{write1,dr1,target1};bitset<2*N> possible;possible.set();possible.reset(key1);possible.reset(2*drop);possible.reset(2*drop+1);bool failed=false;
     for(int orig:{drop,keep,helper1}){for(int bit:{0,1}){for(int win:contexts[orig][bit]){
      bitset<2*N> visited;
      if(!run(drop,keep,orig,bit,win,key1,row1,-1,{},&visited)){failed=true;possible &= visited;}
      if(possible.none())break;
     }if(possible.none())break;}if(possible.none())break;}
     if(!failed){out<<"ONE "<<drop<<' '<<keep<<' '<<offsets[drop]<<' '<<helper1<<' '<<key1%2<<' '<<write1<<' '<<dr1<<' '<<target1<<'\n';out.flush();survivors++;continue;}
     for(int key2=0;key2<2*N;key2++)if(possible[key2]){
      secondkeys++;int helper2=key2/2;
      for(int target2=0;target2<=N;target2++)if(target2!=drop)for(int write2:{0,1})for(int dr2:{-1,1}){
       secondrows++;Row row2{write2,dr2,target2};bool good=true;
       for(int orig:{drop,keep,helper1,helper2})for(int bit:{0,1})if(!contexts[orig][bit].empty()&&good)
         good=run(drop,keep,orig,bit,contexts[orig][bit][0],key1,row1,key2,row2);
       if(!good)continue;reps++;
       for(int orig:{drop,keep,helper1,helper2})for(int bit:{0,1})for(int win:contexts[orig][bit])if(good)
         good=run(drop,keep,orig,bit,win,key1,row1,key2,row2);
       if(good){survivors++;out<<"SURVIVOR "<<drop<<' '<<keep<<' '<<offsets[drop]<<' '<<helper1<<' '<<key1%2<<' '<<write1<<' '<<dr1<<' '<<target1<<' '<<helper2<<' '<<key2%2<<' '<<write2<<' '<<dr2<<' '<<target2<<'\n';out.flush();cerr<<"SURVIVOR "<<drop<<' '<<keep<<'\n';}
      }
     }
    }
   }
  }
  if(drop%10==9)cerr<<"drop "<<drop+1<<" first_rows "<<firstrows<<" second_rows "<<secondrows<<" survivors "<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
 }
 cout<<"pairs "<<pairs<<" first_keys "<<firstkeys<<" first_rows "<<firstrows<<" second_keys "<<secondkeys<<" second_rows "<<secondrows<<" representative_pass "<<reps<<" survivors "<<survivors<<" plain "<<plain<<'\n';
}
