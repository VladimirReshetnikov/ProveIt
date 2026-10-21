/* Finite whole-primitive candidate search. No local one-step endpoint rule. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
enum {NQ=1024,MAXSZ=512,MAXFR=7000};
typedef struct {int w,d,q;} Row;
typedef struct {int ordinal,positive,q,h,ticks;unsigned char initial[MAXSZ],expected[MAXSZ];} Frame;
Row base[NQ][2],tab[NQ][2];int live[NQ],states[NQ],ns;
int witness[NQ][2][2],nf,sz,off;Frame frames[MAXFR];
unsigned long long tests=0,ticks=0;int dispatch,relax_spares,general_frames,drop_tag_mode,drop_move_flip;
int live_registers=0,clear_macros=0;unsigned char clear_words[8][2][52];
unsigned char open_prefixes[8][52];int open_lengths[8];
unsigned char interval_words[8][2][52];int interval_enabled[8];
int anchor=84,gauge=0,expected_registers[MAXFR][9],input_blocks[MAXFR];
unsigned char snapshots[MAXFR][MAXSZ];int snapshot_head[MAXFR],snapshot_active[MAXFR],snapshot_steps[MAXFR];
int cached_keep=-2,cached_drop=-2;
int cache_enabled=0,adaptive_anchor=0,count_prefix_steps=0;
int cycle_prune=0;uint32_t quiet_epoch=0,quiet_seen[NQ][MAXSZ];
int edit_mode=0,edit_q[2],edit_bit[2];
void next_quiet_epoch(void){
 if(++quiet_epoch==0){memset(quiet_seen,0,sizeof(quiet_seen));quiet_epoch=1;}
}

int block_values(int h,unsigned char *t,int *first_nine){
 int first=h+52;while(first<sz&&!t[first])first++;
 int last=sz-1;while(last>=0&&!t[last])last--;
 int p=first+1,count=0;
 while(p<last){
  if(t[p]||!t[p+1])return -1;
  int start=++p;while(p<sz&&t[p])p++;
  if(count<9&&first_nine)first_nine[count]=p-start-1;
  count++;
 }
 return p==last+1?count:-1;
}

int expected_matches(Frame *f,unsigned char *t){
 if(!memcmp(t,f->expected,sz))return 1;
 if(!relax_spares||!(f->positive&2))return 0;
 int last=sz-1;while(last>=0&&!f->expected[last])last--;
 if(last<2||last+1>=sz||!f->expected[last-1]||f->expected[last-2])return 0;
 /* CI may append nothing or append a block of value 0, 1, or 2.
    The baseline appended block is the final pair of ones. */
 if(memcmp(t,f->expected,last-1)||memcmp(t+last+2,f->expected+last+2,sz-last-2))return 0;
 int a=t[last-1],b=t[last],c=t[last+1];
 return (!a&&!b&&!c)||(a&&!b&&!c)||(a&&b&&!c)||(a&&b&&c);
}

int clean_dispatch(int h,unsigned char *t){
 if(h<1||h+64>=sz||!t[h-1])return 0;
 for(int x=0;x<h-1;x++)if(t[x])return 0;
 int first=h+52;
 while(first<sz&&!t[first])first++;
 if(first<h+64||first==sz)return 0;
 int last=sz-1;while(last>=0&&!t[last])last--;
 int p=first+1,count=0;
 while(p<last){
  if(t[p]||!t[p+1])return 0;
  p++;while(p<sz&&t[p])p++;count++;
 }
 return p==last+1&&count>=10;
}
int generalized_matches(int k,int h,unsigned char *t){
 Frame *f=&frames[k];int regs[9];
 if(h<1||h+64>=sz)return 0;
 for(int x=0;x<52;x++)if(t[h+x]!=f->expected[f->h+x])return 0;
 int n=block_values(h,t,regs);
 if(n<input_blocks[k])return 0;
 int phy[9]={6,2,0,4,3,7,8,5,1},mask=live_registers?(f->positive>>6)&511:511;
 for(int j=0;j<9;j++)if((mask>>j&1)&&regs[phy[j]]!=expected_registers[k][phy[j]])return 0;
 return 1;
}
int internal_macro_frame(Frame *f,int origin,unsigned char *t){
 if(!clear_macros||!(f->positive&4))return 0;
 int id=(f->positive>>3)&7;
 if(interval_enabled[id])return memcmp(t+origin,interval_words[id][0],52)>=0&&memcmp(t+origin,interval_words[id][1],52)<0;
 if(open_lengths[id])return !memcmp(t+origin,open_prefixes[id],open_lengths[id]);
 return !memcmp(t+origin,clear_words[id][0],52)||!memcmp(t+origin,clear_words[id][1],52);
}
int test_partial(int k,int keep,int drop,int undefined){
 tests++;Frame *f=&frames[k];unsigned char t[MAXSZ];
 if(cycle_prune)next_quiet_epoch();
 int q=dispatch,h=off-gauge,limit=4*f->ticks+1600;
 if(keep==cached_keep&&drop==cached_drop){
  if(!snapshot_active[k])return 1;
  memcpy(t,snapshots[k],sz);q=keep;h=snapshot_head[k];if(count_prefix_steps)limit-=snapshot_steps[k];
 }else memcpy(t,f->initial,sz);
 for(int step=0;step<limit;step++){
  if(q==254||q==drop||!live[q]||h<0||h>=sz)return 0;
  if(edit_mode){if(undefined>=0&&q==edit_q[undefined]&&t[h]==edit_bit[undefined])return 2;}
  else if(q==keep&&t[h]==undefined)return 2;
  if(cycle_prune){
   if(quiet_seen[q][h]==quiet_epoch)return 0;
   quiet_seen[q][h]=quiet_epoch;
  }
  Row r=tab[q][t[h]];
  if(cycle_prune&&t[h]!=r.w)next_quiet_epoch();
  t[h]=r.w;h+=r.d;q=r.q;ticks++;
  if(q==254||(q==dispatch&&clean_dispatch(h+gauge,t))){
   if(q!=254&&internal_macro_frame(f,h+gauge,t))continue;
   int expectedq=f->q==254?254:dispatch;
   if(q!=expectedq)return 0;
   if(general_frames)return q==254||generalized_matches(k,h+gauge,t);
   return h==f->h-(q==254?0:gauge)&&expected_matches(f,t);
  }
 }
 return 0;
}
int test(int k,int keep,int drop){return test_partial(k,keep,drop,-1);}
int phi(int q,int keep,int drop){return q==drop?keep:q;}
void prepare_snapshots(int keep,int drop){
 cached_keep=keep;cached_drop=drop;
 for(int k=0;k<nf;k++){
  Frame *f=&frames[k];unsigned char *t=snapshots[k];memcpy(t,f->initial,sz);
  int q=anchor,h=off-gauge,previous_head=-1,previous_move=0;snapshot_active[k]=0;
  for(int step=0;step<f->ticks+5;step++){
   if(q==keep||q==drop){
    if(q==drop&&previous_head>=0&&(drop_tag_mode==1||(drop_tag_mode==2&&previous_move==-1)||(drop_tag_mode==3&&previous_move==1)))t[previous_head]^=1;
    if(q==drop&&previous_head>=0&&drop_move_flip)h-=2*previous_move;
    snapshot_head[k]=h;snapshot_active[k]=1;snapshot_steps[k]=step;break;
   }
   if(q==254)break;
   if(step&&q==anchor&&clean_dispatch(h+gauge,t)){
    int internal=0;
    internal=internal_macro_frame(f,h+gauge,t);
    if(!internal)break;
   }
   Row r=base[q][t[h]];t[h]=r.w;previous_head=h;previous_move=r.d;h+=r.d;q=r.q;
  }
 }
}
void configure_pair(int keep,int drop){
 if(adaptive_anchor){anchor=(keep==75||drop==75)?84:75;gauge=anchor==75?1:0;dispatch=phi(anchor,keep,drop);}
 for(int si=0;si<ns;si++)for(int c=0;c<2;c++){
  int s=states[si];Row r=base[s][c];
  if(r.q==drop&&(drop_tag_mode==1||(drop_tag_mode==2&&r.d==-1)||(drop_tag_mode==3&&r.d==1)))r.w^=1;
  if(r.q==drop&&drop_move_flip)r.d=-r.d;
  r.q=phi(r.q,keep,drop);tab[s][c]=r;
 }
 if(cache_enabled)prepare_snapshots(keep,drop);
}
int first_pair_read(int k,int a,int b){
 if(a==cached_keep&&b==cached_drop)return snapshot_active[k]?snapshots[k][snapshot_head[k]]:-1;
 Frame *f=&frames[k];unsigned char t[MAXSZ];memcpy(t,f->initial,sz);
 int q=anchor,h=off-gauge;
 for(int step=0;step<f->ticks+5;step++){
  if(q==254||h<0||h>=sz)return -1;
  if(q==a||q==b)return t[h];
  Row r=base[q][t[h]];t[h]=r.w;h+=r.d;q=r.q;
 }
 return -1;
}
void remember_case(int *cases,int *ncase,int k){
 for(int u=0;u<*ncase;u++)if(cases[u]==k)return;
 memmove(cases+1,cases,*ncase*sizeof(int));cases[0]=k;(*ncase)++;
}
int main(int argc,char **argv){
 if(argc<5||argc>7){fprintf(stderr,"usage: %s table.tm frames.bin witnesses.txt hits.txt [sole | both pairs.txt]\n",argv[0]);return 2;}
 FILE *f=fopen(argv[1],"r");char line[128],dir;int q,b,w,z;
 while(fgets(line,sizeof(line),f))if(sscanf(line,"%d %d %d %c %d",&q,&b,&w,&dir,&z)==5){base[q][b]=(Row){w,dir=='R'?1:-1,z};live[q]=1;}
 fclose(f);for(q=0;q<NQ;q++)if(live[q])states[ns++]=q;
 f=fopen(argv[2],"rb");if(!f)return 3;
 fread(&nf,4,1,f);fread(&sz,4,1,f);fread(&off,4,1,f);
 if(nf>MAXFR||sz!=MAXSZ)return 4;
 for(int i=0;i<nf;i++){
  Frame *x=&frames[i];fread(&x->ordinal,4,1,f);fread(&x->positive,4,1,f);fread(&x->q,4,1,f);fread(&x->h,4,1,f);fread(&x->ticks,4,1,f);
  fread(x->initial,1,sz,f);fread(x->expected,1,sz,f);
 }
 fclose(f);memset(witness,-1,sizeof(witness));
 f=fopen(argv[3],"r");int i,j;while(fscanf(f,"%d%d%d%d",&q,&b,&i,&j)==4){witness[q][b][0]=i;witness[q][b][1]=j;}fclose(f);
 FILE *out=fopen(argv[4],"w");int pairs=0,actions=0,hits=0,witness_survivors=0;clock_t beg=clock();
 relax_spares=getenv("RELAX_SPARES")!=NULL;
 general_frames=getenv("GENERAL_FRAMES")!=NULL;
 drop_tag_mode=getenv("DROP_TAG_MODE")?atoi(getenv("DROP_TAG_MODE")):0;
 drop_move_flip=getenv("DROP_MOVE_FLIP")!=NULL;
 live_registers=getenv("LIVE_REGISTERS")!=NULL;
 if(getenv("CLEAR_MACROS")){
  FILE *cf=fopen(getenv("CLEAR_MACROS"),"r");if(!cf)return 7;
  int id;char p0[100],p1[100];
  while(fscanf(cf,"%d%99s%99s",&id,p0,p1)==3){
   if(id<0||id>=8||strlen(p0)>52||strlen(p1)>52)return 8;
   for(int k=0;p0[k];k++)clear_words[id][0][k]=p0[k]=='1';
   for(int k=0;p1[k];k++)clear_words[id][1][k]=p1[k]=='1';
  }
  fclose(cf);clear_macros=1;
 }
 if(getenv("OPEN_MACROS")){
  FILE *cf=fopen(getenv("OPEN_MACROS"),"r");if(!cf)return 11;
  int id;char prefix[100];
  while(fscanf(cf,"%d%99s",&id,prefix)==2){
   if(id<0||id>=8||strlen(prefix)>52)return 12;
   open_lengths[id]=(int)strlen(prefix);
   for(int k=0;prefix[k];k++)open_prefixes[id][k]=prefix[k]=='1';
  }
  fclose(cf);clear_macros=1;
 }
 if(getenv("INTERVAL_MACROS")){
  FILE *cf=fopen(getenv("INTERVAL_MACROS"),"r");if(!cf)return 13;
  int id;char low[100],high[100];
  while(fscanf(cf,"%d%99s%99s",&id,low,high)==3){
   if(id<0||id>=8||strlen(low)>52||strlen(high)>52)return 14;
   interval_enabled[id]=1;
   for(int k=0;low[k];k++)interval_words[id][0][k]=low[k]=='1';
   for(int k=0;high[k];k++)interval_words[id][1][k]=high[k]=='1';
   if(memcmp(interval_words[id][0],interval_words[id][1],52)>=0)return 15;
  }
  fclose(cf);clear_macros=1;
 }
 cache_enabled=argc==7;
 count_prefix_steps=getenv("COUNT_PREFIX_STEPS")!=NULL;
 cycle_prune=getenv("CYCLE_PRUNE")!=NULL;
 adaptive_anchor=getenv("ADAPTIVE_ANCHOR")!=NULL;
 if(getenv("FRAME_ANCHOR")&&atoi(getenv("FRAME_ANCHOR"))==75){anchor=75;gauge=1;}
 for(int k=0;k<nf;k++){
  input_blocks[k]=block_values(off,frames[k].initial,NULL);
  if(frames[k].q!=254)block_values(frames[k].h,frames[k].expected,expected_registers[k]);
 }
 memcpy(tab,base,sizeof(tab));dispatch=anchor;
 for(int k=0;k<nf;k++)if(!test(k,-1,-1)){fprintf(stderr,"BASELINE_FAILED %d\n",k);return 5;}
 printf("BASELINE_PASS %d frames RELAX_SPARES=%d GENERAL_FRAMES=%d ANCHOR=%d GAUGE=%d DROP_TAG_MODE=%d LIVE_REGISTERS=%d CLEAR_MACROS=%d DROP_MOVE_FLIP=%d COUNT_PREFIX_STEPS=%d\n",nf,relax_spares,general_frames,anchor,gauge,drop_tag_mode,live_registers,clear_macros,drop_move_flip,count_prefix_steps);fflush(stdout);
 if(getenv("VERIFY_ONLY")){fclose(out);return 0;}
 if(getenv("EDIT_PAIR")){
  int drop;
  if(sscanf(getenv("EDIT_PAIR"),"%d%d%d%d%d",&edit_q[0],&edit_bit[0],&edit_q[1],&edit_bit[1],&drop)!=5)return 10;
  edit_mode=1;Row allowed[2][4*(NQ+1)];int nallowed[2]={0,0};
  int cases[MAXFR],ncase=0;unsigned long long fullactions=0;
  for(int slot=0;slot<2;slot++)for(int y=0;y<2;y++){
   int n=witness[edit_q[slot]][edit_bit[slot]][y];if(n>=0)remember_case(cases,&ncase,n);
  }
  for(int slot=0;slot<2;slot++){
   for(int ww=0;ww<2;ww++)for(int dd=-1;dd<=1;dd+=2)for(int zi=0;zi<=ns;zi++){
    int zz=zi==ns?254:states[zi];if(zz==drop)continue;
    actions++;tab[edit_q[slot]][edit_bit[slot]]=(Row){ww,dd,zz};int pass=1;
    for(int ci=0;ci<ncase;ci++)if(!test_partial(cases[ci],-1,drop,1-slot)){pass=0;break;}
    if(!pass)continue;
    for(int k=0;k<nf;k++)if(!test_partial(k,-1,drop,1-slot)){pass=0;remember_case(cases,&ncase,k);break;}
    if(pass)allowed[slot][nallowed[slot]++]=(Row){ww,dd,zz};
   }
  }
  printf("EDIT_ALLOWED %d %d\n",nallowed[0],nallowed[1]);fflush(stdout);
  for(int x=0;x<nallowed[0];x++)for(int y=0;y<nallowed[1];y++){
   fullactions++;tab[edit_q[0]][edit_bit[0]]=allowed[0][x];tab[edit_q[1]][edit_bit[1]]=allowed[1][y];int pass=1;
   for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],-1,drop)){pass=0;break;}
   if(!pass)continue;
   witness_survivors++;
   for(int k=0;k<nf;k++)if(!test(k,-1,drop)){pass=0;remember_case(cases,&ncase,k);break;}
   if(!pass)continue;
   Row a=allowed[0][x],b=allowed[1][y];hits++;
   printf("FOUND_EDIT %d %d %d %d %d %d %d %d %d %d %d\n",drop,edit_q[0],edit_bit[0],a.w,a.d,a.q,edit_q[1],edit_bit[1],b.w,b.d,b.q);fflush(stdout);
   fprintf(out,"%d %d %d %d %d %d %d %d %d %d %d\n",drop,edit_q[0],edit_bit[0],a.w,a.d,a.q,edit_q[1],edit_bit[1],b.w,b.d,b.q);fflush(out);
  }
  printf("DONE_EDIT actions=%d full_actions=%llu witness_survivors=%d hits=%d tests=%llu steps=%llu seconds=%.2f\n",actions,fullactions,witness_survivors,hits,tests,ticks,(double)(clock()-beg)/CLOCKS_PER_SEC);
  fclose(out);return 0;
 }
 if(getenv("NEUTRAL_SCAN")){
  int focus[NQ]={0},focused=0;
  if(getenv("FOCUS_TARGETS")){
   const char *at=getenv("FOCUS_TARGETS");char *end;
   while(*at){long x=strtol(at,&end,10);if(end==at)break;if(x>=0&&x<NQ){focus[x]=1;focused=1;}at=end;}
  }
  for(int qi=0;qi<ns;qi++)for(int read=0;read<2;read++){
   int s=states[qi],old=base[s][read].q;
   if(old==254||(focused&&!focus[old])||s==old)continue;
   pairs++;memcpy(tab,base,sizeof(tab));int cases[MAXFR],ncase=0;
   for(int x=0;x<3;x++)for(int y=0;y<2;y++){
    int n=witness[x?old:s][x?x-1:read][y];
    if(n>=0)remember_case(cases,&ncase,n);
   }
   for(int ww=0;ww<2;ww++)for(int dd=-1;dd<=1;dd+=2)for(int zi=0;zi<=ns;zi++){
    int zz=zi==ns?254:states[zi];if(zz==old)continue;
    actions++;tab[s][read]=(Row){ww,dd,zz};int pass=1;
    for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],-1,-1)){pass=0;break;}
    if(!pass)continue;
    witness_survivors++;
    for(int k=0;k<nf;k++)if(!test(k,-1,-1)){pass=0;remember_case(cases,&ncase,k);break;}
    if(!pass)continue;
    hits++;printf("FOUND_NEUTRAL %d %d %d %d %d %d\n",s,read,old,ww,dd,zz);fflush(stdout);
    fprintf(out,"%d %d %d %d %d %d\n",s,read,old,ww,dd,zz);fflush(out);
   }
   printf("PROGRESS_NEUTRAL rows=%d actions=%d witness_survivors=%d hits=%d seconds=%.2f\n",pairs,actions,witness_survivors,hits,(double)(clock()-beg)/CLOCKS_PER_SEC);fflush(stdout);
  }
  printf("DONE_NEUTRAL rows=%d actions=%d witness_survivors=%d hits=%d tests=%llu steps=%llu seconds=%.2f\n",pairs,actions,witness_survivors,hits,tests,ticks,(double)(clock()-beg)/CLOCKS_PER_SEC);
  fclose(out);return 0;
 }
 if(getenv("FIXED_REPAIR")){
  int p,c,drop,fw,fd,fq;
  if(sscanf(getenv("FIXED_REPAIR"),"%d%d%d%d%d%d",&p,&c,&drop,&fw,&fd,&fq)!=6)return 9;
  for(int qi=0;qi<ns;qi++)for(int read=0;read<2;read++){
   int s=states[qi];if(s==drop||(s==p&&read==c))continue;
   pairs++;memcpy(tab,base,sizeof(tab));tab[p][c]=(Row){fw,fd,fq};
   int cases[MAXFR],ncase=0;
   for(int x=0;x<4;x++)for(int y=0;y<2;y++){
    int state=x==0?p:x==3?s:drop;
    int bit=x==0?c:x==3?read:x-1;
    int n=witness[state][bit][y];
    if(n>=0)remember_case(cases,&ncase,n);
   }
   for(int ww=0;ww<2;ww++)for(int dd=-1;dd<=1;dd+=2)for(int zi=0;zi<=ns;zi++){
    int zz=zi==ns?254:states[zi];if(zz==drop)continue;
    actions++;tab[s][read]=(Row){ww,dd,zz};int pass=1;
    for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],-1,drop)){pass=0;break;}
    if(!pass)continue;
    witness_survivors++;
    for(int k=0;k<nf;k++)if(!test(k,-1,drop)){pass=0;remember_case(cases,&ncase,k);break;}
    if(!pass)continue;
    hits++;printf("FOUND_REPAIR %d %d %d %d %d %d %d %d %d %d %d\n",p,c,drop,fw,fd,fq,s,read,ww,dd,zz);fflush(stdout);
    fprintf(out,"%d %d %d %d %d %d %d %d %d %d %d\n",p,c,drop,fw,fd,fq,s,read,ww,dd,zz);fflush(out);
   }
   if(pairs%20==0){printf("PROGRESS_REPAIR rows=%d actions=%d witness_survivors=%d hits=%d seconds=%.2f\n",pairs,actions,witness_survivors,hits,(double)(clock()-beg)/CLOCKS_PER_SEC);fflush(stdout);}
  }
  printf("DONE_REPAIR rows=%d actions=%d witness_survivors=%d hits=%d tests=%llu steps=%llu seconds=%.2f\n",pairs,actions,witness_survivors,hits,tests,ticks,(double)(clock()-beg)/CLOCKS_PER_SEC);
  fclose(out);return 0;
 }
 if(argc==7&&(!strcmp(argv[5],"both")||!strcmp(argv[5],"both_pre"))){
  FILE *pf=fopen(argv[6],"r");int a,drop;
  unsigned long long fullactions=0,partial_survivors=0;
  while(fscanf(pf,"%d%d",&a,&drop)==2){
   pairs++;dispatch=phi(anchor,a,drop);
   configure_pair(a,drop);
   int cases[MAXFR],ncase=0;
   for(int x=0;x<2;x++)for(int read=0;read<2;read++)for(int y=0;y<2;y++){
    int n=witness[x?drop:a][read][y],exists=0;
    for(int u=0;u<ncase;u++)if(cases[u]==n)exists=1;
    if(n>=0&&!exists)cases[ncase++]=n;
   }
   int initial_reads[2]={0,0};
   for(int ci=0;ci<ncase;ci++){int r=first_pair_read(cases[ci],a,drop);if(r>=0)initial_reads[r]++;}
   int firstrow=initial_reads[1]>initial_reads[0]?1:0,secondrow=1-firstrow;
   int hits_before=hits;
   if(!strcmp(argv[5],"both_pre")){
    Row allowed[2][4*(NQ+1)];int nallowed[2]={0,0};
    for(int rr=0;rr<2;rr++){
     int read=rr?secondrow:firstrow;
     for(int ww=0;ww<2;ww++)for(int dd=-1;dd<=1;dd+=2)for(int zi=0;zi<=ns;zi++){
      int zz=zi==ns?254:states[zi];if(zz==drop)continue;
      actions++;tab[a][read]=(Row){ww,dd,zz};int pass=1;
      for(int ci=0;ci<ncase;ci++)if(!test_partial(cases[ci],a,drop,1-read)){pass=0;break;}
      if(!pass)continue;
      for(int k=0;k<nf;k++)if(!test_partial(k,a,drop,1-read)){
       pass=0;remember_case(cases,&ncase,k);break;
      }
      if(!pass)continue;
      allowed[read][nallowed[read]++]=tab[a][read];partial_survivors++;
     }
    }
    for(int x=0;x<nallowed[0];x++)for(int y=0;y<nallowed[1];y++){
     fullactions++;tab[a][0]=allowed[0][x];tab[a][1]=allowed[1][y];int pass=1;
     for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],a,drop)){pass=0;break;}
     if(!pass)continue;
     witness_survivors++;
     for(int k=0;k<nf;k++)if(!test(k,a,drop)){pass=0;remember_case(cases,&ncase,k);break;}
     if(!pass)continue;
     Row r0=tab[a][0],r1=tab[a][1];hits++;
     printf("FOUND_BOTH %d %d %d %d %d %d %d %d\n",a,drop,r0.w,r0.d,r0.q,r1.w,r1.d,r1.q);fflush(stdout);
     fprintf(out,"%d %d %d %d %d %d %d %d\n",a,drop,r0.w,r0.d,r0.q,r1.w,r1.d,r1.q);fflush(out);
    }
    if(pairs<=20||pairs%20==0||hits>hits_before){printf("PAIR_ALLOWED %d %d %d %d\n",a,drop,nallowed[0],nallowed[1]);fflush(stdout);}
    goto pair_done;
   }
   for(int w0=0;w0<2;w0++)for(int d0=-1;d0<=1;d0+=2)for(int z0i=0;z0i<=ns;z0i++){
    int z0=z0i==ns?254:states[z0i];if(z0==drop)continue;
    actions++;tab[a][firstrow]=(Row){w0,d0,z0};int pass=1;
    for(int ci=0;ci<ncase;ci++)if(!test_partial(cases[ci],a,drop,secondrow)){pass=0;break;}
    if(!pass)continue;
    partial_survivors++;
    for(int w1=0;w1<2;w1++)for(int d1=-1;d1<=1;d1+=2)for(int z1i=0;z1i<=ns;z1i++){
     int z1=z1i==ns?254:states[z1i];if(z1==drop)continue;
     fullactions++;tab[a][secondrow]=(Row){w1,d1,z1};pass=1;
     for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],a,drop)){pass=0;break;}
     if(!pass)continue;
     witness_survivors++;
     for(int k=0;k<nf;k++)if(!test(k,a,drop)){
      pass=0;remember_case(cases,&ncase,k);
      break;
     }
     if(!pass)continue;
     Row r0=tab[a][0],r1=tab[a][1];
     hits++;printf("FOUND_BOTH %d %d %d %d %d %d %d %d\n",a,drop,r0.w,r0.d,r0.q,r1.w,r1.d,r1.q);fflush(stdout);
     fprintf(out,"%d %d %d %d %d %d %d %d\n",a,drop,r0.w,r0.d,r0.q,r1.w,r1.d,r1.q);fflush(out);
    }
   }
pair_done:
   if(pairs<=20||pairs%20==0||hits>hits_before){printf("PROGRESS_BOTH pairs=%d first_actions=%d partial_survivors=%llu full_actions=%llu witness_survivors=%d hits=%d learned=%d seconds=%.2f\n",pairs,actions,partial_survivors,fullactions,witness_survivors,hits,ncase,(double)(clock()-beg)/CLOCKS_PER_SEC);fflush(stdout);}
  }
  printf("DONE_BOTH pairs=%d first_actions=%d partial_survivors=%llu full_actions=%llu witness_survivors=%d hits=%d tests=%llu steps=%llu seconds=%.2f\n",pairs,actions,partial_survivors,fullactions,witness_survivors,hits,tests,ticks,(double)(clock()-beg)/CLOCKS_PER_SEC);
  fclose(pf);fclose(out);return 0;
 }
 if(argc==6&&!strcmp(argv[5],"sole")){
  FILE *candidate_out=getenv("WITNESS_CANDIDATES")?fopen(getenv("WITNESS_CANDIDATES"),"w"):NULL;
  for(int bi=0;bi<ns;bi++){
   int drop=states[bi],count=0,p=-1,c=-1;
   if(drop==0||drop==anchor)continue;
   for(int qi=0;qi<ns;qi++)for(int read=0;read<2;read++)if(base[states[qi]][read].q==drop){count++;p=states[qi];c=read;}
   if(count!=1||p==drop)continue;
   pairs++;memcpy(tab,base,sizeof(tab));dispatch=anchor;
   int cases[6],ncase=0;
   for(int x=0;x<3;x++)for(int y=0;y<2;y++){
    int n=witness[x==2?p:drop][x==2?c:x][y],exists=0;
    for(int u=0;u<ncase;u++)if(cases[u]==n)exists=1;
    if(n>=0&&!exists)cases[ncase++]=n;
   }
   for(int ww=0;ww<2;ww++)for(int dd=-1;dd<=1;dd+=2)for(int zi=0;zi<=ns;zi++){
    int zz=zi==ns?254:states[zi];if(zz==drop)continue;
    actions++;tab[p][c]=(Row){ww,dd,zz};int pass=1;
    for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],-1,drop)){pass=0;break;}
    if(!pass)continue;
    witness_survivors++;
    if(candidate_out){fprintf(candidate_out,"%d %d %d %d %d %d\n",p,c,drop,ww,dd,zz);fflush(candidate_out);}
    for(int k=0;k<nf;k++)if(!test(k,-1,drop)){pass=0;break;}
    if(!pass)continue;
    hits++;printf("FOUND_SOLE %d %d %d %d %d %d\n",p,drop,c,ww,dd,zz);fflush(stdout);
    fprintf(out,"%d %d %d %d %d %d\n",p,drop,c,ww,dd,zz);fflush(out);
   }
  }
  printf("DONE_SOLE states=%d actions=%d witness_survivors=%d hits=%d tests=%llu steps=%llu seconds=%.2f\n",pairs,actions,witness_survivors,hits,tests,ticks,(double)(clock()-beg)/CLOCKS_PER_SEC);
  if(candidate_out)fclose(candidate_out);
  fclose(out);return 0;
 }
 for(int ai=0;ai<ns;ai++)for(int bi=ai+1;bi<ns;bi++){
  int a=states[ai],drop=states[bi],same=0,read=-1;
  for(int c=0;c<2;c++){
   Row x=base[a][c],y=base[drop][c];
   if(x.w==y.w&&x.d==y.d&&phi(x.q,a,drop)==phi(y.q,a,drop))same++;
   else read=c;
  }
  if(same!=1)continue;
  pairs++;dispatch=phi(anchor,a,drop);
  configure_pair(a,drop);
  int cases[4],ncase=0;
  for(int x=0;x<2;x++)for(int y=0;y<2;y++){
   int n=witness[x?drop:a][read][y],exists=0;
   for(int u=0;u<ncase;u++)if(cases[u]==n)exists=1;
   if(n>=0&&!exists)cases[ncase++]=n;
  }
  for(int ww=0;ww<2;ww++)for(int dd=-1;dd<=1;dd+=2)for(int zi=0;zi<=ns;zi++){
   int zz=zi==ns?254:states[zi];if(zz==drop)continue;
   actions++;tab[a][read]=(Row){ww,dd,zz};int pass=1;
   for(int ci=0;ci<ncase;ci++)if(!test(cases[ci],a,drop)){pass=0;break;}
   if(!pass)continue;
   witness_survivors++;
   for(int k=0;k<nf;k++)if(!test(k,a,drop)){pass=0;break;}
   if(!pass)continue;
   hits++;printf("FOUND %d %d %d %d %d %d\n",a,drop,read,ww,dd,zz);fflush(stdout);
   fprintf(out,"%d %d %d %d %d %d\n",a,drop,read,ww,dd,zz);fflush(out);
  }
  if(pairs%10==0){printf("PROGRESS pairs=%d actions=%d witness_survivors=%d hits=%d seconds=%.2f\n",pairs,actions,witness_survivors,hits,(double)(clock()-beg)/CLOCKS_PER_SEC);fflush(stdout);}
 }
 printf("DONE pairs=%d actions=%d witness_survivors=%d hits=%d tests=%llu steps=%llu seconds=%.2f\n",pairs,actions,witness_survivors,hits,tests,ticks,(double)(clock()-beg)/CLOCKS_PER_SEC);
 fclose(out);return 0;
}
