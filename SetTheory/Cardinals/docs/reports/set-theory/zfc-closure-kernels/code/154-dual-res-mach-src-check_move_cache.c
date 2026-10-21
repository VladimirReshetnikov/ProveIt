/* Regression for the cache optimization with flipped incoming movement. */
#define main search_main
#include "whole_primitive_folds.c"
#undef main
int main(int argc,char **argv){
 int result=search_main(argc,argv);if(result)return result;
 cache_enabled=1;drop_move_flip=1;general_frames=1;count_prefix_steps=1;
 FILE *pf=fopen(argv[6],"r");if(!pf)return 20;
 int keep,drop,np=0;unsigned long long compared=0;
 while(np<12&&fscanf(pf,"%d%d",&keep,&drop)==2){
  np++;configure_pair(keep,drop);
  for(int action=0;action<16;action++){
   tab[keep][0]=(Row){action&1,(action&2)?1:-1,states[(action*37+np)%ns]};
   tab[keep][1]=(Row){(action>>2)&1,(action&8)?1:-1,states[(action*71+np)%ns]};
   if(tab[keep][0].q==drop)tab[keep][0].q=254;
   if(tab[keep][1].q==drop)tab[keep][1].q=254;
   for(int i=0;i<nf;i++){
    /* Every macro and a deterministic sparse sample of ordinary frames. */
    if(!(frames[i].positive&4)&&i%97)continue;
    int a=test(i,keep,drop);
    cached_keep=-2;cached_drop=-2;
    int b=test(i,keep,drop);
    cached_keep=keep;cached_drop=drop;compared++;
    if(a!=b){
     fprintf(stderr,"CACHE_MISMATCH pair=%d,%d action=%d frame=%d cached=%d full=%d active=%d snaphead=%d rows=%d,%d,%d;%d,%d,%d\n",keep,drop,action,i,a,b,snapshot_active[i],snapshot_head[i],tab[keep][0].w,tab[keep][0].d,tab[keep][0].q,tab[keep][1].w,tab[keep][1].d,tab[keep][1].q);
     unsigned char t[MAXSZ];memcpy(t,frames[i].initial,sz);int q=dispatch,h=off-gauge;
     for(int st=0;st<frames[i].ticks+10;st++){
      if(q==keep){fprintf(stderr,"FULL_ENTRY step=%d head=%d tape_match=%d\n",st,h,!memcmp(t,snapshots[i],sz));break;}
      if(q==254||h<0||h>=sz){fprintf(stderr,"FULL_PREFIX_ABORT %d %d %d\n",st,q,h);break;}
      Row x=tab[q][t[h]];t[h]=x.w;h+=x.d;q=x.q;
     }
     return 21;
    }
   }
  }
 }
 fclose(pf);printf("MOVE_CACHE_PASS pairs=%d compared=%llu\n",np,compared);return 0;
}
