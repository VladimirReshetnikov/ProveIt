#include <bits/stdc++.h>
using namespace std;
struct Tr{int w,d,n;};Tr T0[255][2];
int main(int argc,char**argv){
 ifstream in(argv[1]);string line;int mode=argc>2?atoi(argv[2]):0,LIMIT=argc>3?atoi(argv[3]):1000000;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;T0[q][b]={w,d=='R'?1:-1,n};}
 const int SZ=20000,Z=5000;vector<unsigned char>a(SZ);long long steps=0,cands=0;int found=0;
 auto check=[&](int h,int&gap,vector<int>&regs)->bool{
  int lo=0;while(lo<SZ&&!a[lo])++lo;if(lo!=h-1)return false;
  int j=h;while(j<SZ&&!a[j])++j;gap=j-h;if(gap<38||gap>5000)return false;
  ++j;regs.clear();
  while(j+1<SZ && a[j]==0 && a[j+1]==1){
   j++;int count=0;while(j<SZ&&a[j]){count++;j++;}
   int block=regs.size();if(block<9 && block!=1 && block!=5 && block!=6 && count!=1)return false;
   regs.push_back(count-1);
  }
  if(regs.size()<9)return false;
  for(;j<SZ;j++)if(a[j])return false;return true;
 };
 auto run=[&](Tr T[255][2],int start,int w,int d,int r){
  fill(a.begin(),a.end(),0);int q=start,h=Z;++cands;
  if(mode==3)a[Z+d]=1;
  for(int t=0;t<LIMIT;t++){
   if(q==254||(mode!=2 && q==8)||(mode!=1 && q==5)||h<2||h>=SZ-2)break;
   Tr z=T[q][a[h]];a[h]=z.w;h+=z.d;q=z.n;steps++;
   if(q==96){int gap;vector<int>regs;if(check(h,gap,regs)){
    cout<<"PASS mode="<<mode<<" start="<<start<<" wdr="<<w<<","<<d<<","<<r<<" steps="<<t+1<<" head="<<h-Z<<" gap="<<gap<<" regs=";
    for(int x:regs)cout<<x<<",";cout<<endl;found++;break;
   }}
  }
 };
 if(mode==0 || mode==3){ // 252-state core, folds 5->48, removes unreachable8, try every start
  Tr T[255][2];copy(&T0[0][0],&T0[0][0]+510,&T[0][0]);
  for(int q=0;q<254;q++)for(int b=0;b<2;b++)if(T[q][b].n==5)T[q][b].n=48;
  for(int st=0;st<254;st++)if(st!=5&&st!=8){if(mode==3){run(T,st,-1,-1,48);run(T,st,-1,1,48);}else run(T,st,-1,0,48);}
 }else if(mode==1){ // 253-state: remove8, assign formerly5/1 bootstrap jump freely
  for(int w=0;w<2;w++)for(int d:{-1,1})for(int r=0;r<254;r++)if(r!=8){
   Tr T[255][2];copy(&T0[0][0],&T0[0][0]+510,&T[0][0]);T[5][1]={w,d,r};run(T,0,w,d,r);
  }
 }else if(mode==2){ // 253-state fold5->48 only, preserve8 as possible initial state
  Tr T[255][2];copy(&T0[0][0],&T0[0][0]+510,&T[0][0]);
  for(int q=0;q<254;q++)for(int b=0;b<2;b++)if(T[q][b].n==5)T[q][b].n=48;
  for(int st=0;st<254;st++)if(st!=5)run(T,st,-1,0,48);
 }
 cerr<<"DONE candidates="<<cands<<" steps="<<steps<<" found="<<found<<endl;
}
