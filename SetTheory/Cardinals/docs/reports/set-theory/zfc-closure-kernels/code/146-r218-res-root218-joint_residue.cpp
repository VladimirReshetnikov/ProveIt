// Exact finite abstract reachability: digit0=0, digit1=positive even, digit2=odd.
// The concrete all-natural induction is verified independently in Python.
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
 if(argc!=3)return 2;ifstream in(argv[1]);int n;in>>n;
 constexpr int B=19683,W=(B+63)/64;int pow3[9]={1};for(int j=1;j<9;j++)pow3[j]=pow3[j-1]*3;
 struct Row{int op,r,t0,t1,m;};vector<Row>a(n);for(auto &x:a)in>>x.op>>x.r>>x.t0>>x.t1>>x.m;
 vector<vector<uint64_t>> seen(n,vector<uint64_t>(W));deque<uint32_t> todo;
 auto add=[&](int pc,int mask){uint64_t bit=1ull<<(mask%64);if(!(seen[pc][mask/64]&bit)){seen[pc][mask/64]|=bit;todo.push_back(pc*B+mask);}};
 add(0,2+2*81);long long processed=0,edges=0;
 while(!todo.empty()){
  auto key=todo.front();todo.pop_front();int pc=key/B,mask=key%B;auto x=a[pc];processed++;
  if(x.op==4)continue;
  if(x.op==2||x.op==3){add(x.t0,mask);edges++;continue;}
  int p=pow3[x.r],d=(mask/p)%3;
  if(x.op==0){int z=d==2?1:2;add(x.t0,mask+(z-d)*p);edges++;}
  else if(d==0){add(x.t0,mask);edges++;}
  else if(d==1){add(x.t1,mask+p);edges++;}
  else{
   if(x.m&2){add(x.t1,mask-2*p);edges++;}
   if(x.m&(8|16)){add(x.t1,mask-p);edges++;}
  }
 }
 ofstream out(argv[2],ios::binary);uint32_t header[3]={(uint32_t)n,B,W};out.write((char*)header,sizeof header);
 for(auto const&row:seen)out.write((char*)row.data(),W*sizeof(uint64_t));
 cout<<"JOINT_RESIDUE_COMPLETE profiles "<<processed<<" edges "<<edges<<" rows "<<n<<" bytes "<<(12+n*W*8)<<endl;
}
