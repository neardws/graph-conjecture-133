/* gstat: read graph6 lines from stdin, print invariants used in the manuscript.
   Output per graph (space separated):
   g6 n e T S p r diam hasC4 minL adjdeg2 minDeg
   S   = sum over v of alpha(G[N(v)])   (computed directly, not via 2e-3T)
   p   = order of a longest induced path
   r   = radius, diam = diameter (graphs assumed connected)
   hasC4 = 1 if G contains a 4-cycle as a subgraph
   minL = min over v of 2d(v)-3t(v)   (deletion loss; meaningful for C4-free)
   adjdeg2 = 1 if two adjacent vertices both have degree 2
   Optional argv[1] = pmax: if given, skip graphs with p > pmax (early exit).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
typedef uint32_t set;
static int n;
static set adj[MAXN];

static int popc(set x){ return __builtin_popcount(x); }

static int alpha(set M){
    if(!M) return 0;
    /* branch on a vertex of max degree inside M */
    int best=-1, bd=-1;
    for(set t=M;t;t&=t-1){int v=__builtin_ctz(t); int d=popc(adj[v]&M); if(d>bd){bd=d;best=v;}}
    if(bd==0) return popc(M);
    int v=best;
    int a1=alpha(M&~(1u<<v));
    int a2=1+alpha(M&~(adj[v]|(1u<<v)));
    return a1>a2?a1:a2;
}

static int bestp, cap;
static void dfs(int last, set B, int len){
    if(len>bestp) bestp=len;
    if(bestp>=cap) return;
    set cand = adj[last] & ~B;
    set Bn = B | adj[last] | (1u<<last);
    for(set t=cand;t;t&=t-1){
        int y=__builtin_ctz(t);
        dfs(y, Bn, len+1);
        if(bestp>=cap) return;
    }
}
static int longest_induced_path(int capv){
    bestp=0; cap=capv;
    for(int s=0;s<n;s++){
        dfs(s, 0, 1);  /* B = closed nbhds of all but last; initially empty */
        if(bestp>=cap) break;
    }
    return bestp;
}

static int ecc(int v){
    set seen=1u<<v, fr=seen; int d=0; set all=(n==32)?0xffffffffu:((1u<<n)-1);
    while(seen!=all){
        set nf=0; for(set t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)];
        nf&=~seen; if(!nf) return 1000; seen|=nf; fr=nf; d++;
    }
    return d;
}

static int parse_g6(const char *s){
    const unsigned char *p=(const unsigned char*)s;
    if(*p=='>' ) return 0;
    n=*p++-63; if(n>MAXN||n<1) return 0;
    memset(adj,0,sizeof(adj));
    int k=0; int bits=0; int val=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){
        if(bits==0){ val=*p++-63; bits=6; }
        bits--; if((val>>bits)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
        k++;
    }
    return 1;
}

int main(int argc,char**argv){
    int pmax = argc>1? atoi(argv[1]) : 1000;
    char line[256];
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0;
        if(!parse_g6(line)) continue;
        int p = longest_induced_path(pmax+1);
        if(p>pmax) continue;
        int e=0,T=0,S=0,hasC4=0,minL=1000,adj2=0,mind=1000;
        for(int v=0;v<n;v++){
            int d=popc(adj[v]); e+=d; if(d<mind) mind=d;
            int t=0; for(set q=adj[v];q;q&=q-1){int u=__builtin_ctz(q); if(u>v){} t+=popc(adj[u]&adj[v]);} t/=2;
            T+=t;
            S+=alpha(adj[v]);
            int L=2*d-3*t; if(L<minL) minL=L;
        }
        e/=2; T/=3;
        for(int u=0;u<n&&!hasC4;u++) for(int w=u+1;w<n;w++) if(popc(adj[u]&adj[w])>=2){hasC4=1;break;}
        for(int u=0;u<n;u++) if(popc(adj[u])==2) for(set q=adj[u];q;q&=q-1){int w=__builtin_ctz(q); if(popc(adj[w])==2) adj2=1;}
        int r=1000,dm=0; for(int v=0;v<n;v++){int x=ecc(v); if(x<r)r=x; if(x>dm)dm=x;}
        printf("%s %d %d %d %d %d %d %d %d %d %d %d\n",line,n,e,T,S,p,r,dm,hasC4,minL,adj2,mind);
    }
    return 0;
}
