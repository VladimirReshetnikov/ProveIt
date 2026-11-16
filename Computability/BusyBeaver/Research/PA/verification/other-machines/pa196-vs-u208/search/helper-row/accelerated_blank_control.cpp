#define main accelerated_main
#include "accelerated_blank.cpp"
#undef main
uint64_t rng=0x123456789abcdefULL;
uint64_t nextval(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
int main(){
 Tape a, b;
 for(int trial=0;trial<10000;trial++){
  for(int p=-256;p<256;p++){int x=nextval()&1;a.put(p,x);b.put(p,x);}
  int64_t p=int(nextval()%321)-160,p2=p;int bit=a.get(p),w=nextval()&1,d=(nextval()&1)?1:-1;uint64_t limit=nextval()%97+1;
  auto k=a.consume(p,bit,w,d,limit);uint64_t n=0;
  while(n<limit&&b.get(p2)==bit){b.put(p2,w);p2+=d;n++;}
  if(k!=n||p!=p2){cerr<<"bad steps "<<trial<<"\n";return 1;}
  for(int i=-256;i<256;i++)if(a.get(i)!=b.get(i)){cerr<<"bad tape "<<trial<<" "<<i<<"\n";return 2;}
 }
 // Force long uniform runs over word boundaries; random dense tapes rarely do.
 int forced=0;
 for(int bit=0;bit<=1;bit++)for(int w=0;w<=1;w++)for(int d:{-1,1})
  for(int start:{-100,-65,-64,-1,0,1,63,64,65,100})
   for(int length:{1,2,63,64,65,129}){
    for(int i=-256;i<256;i++){a.put(i,bit);b.put(i,bit);}
    a.put(start+d*length,1-bit);b.put(start+d*length,1-bit);
    int64_t p=start,p2=start;auto k=a.consume(p,bit,w,d,200);uint64_t n=0;
    while(n<200&&b.get(p2)==bit){b.put(p2,w);p2+=d;n++;}
    if(k!=n||p!=p2||n!=uint64_t(length)){cerr<<"forced steps\n";return 3;}
    for(int i=-256;i<256;i++)if(a.get(i)!=b.get(i)){cerr<<"forced tape\n";return 4;}
    forced++;
   }
 cout<<"control_trials 10000 forced "<<forced<<" pass\n";
}
