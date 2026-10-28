"""Characterise leaks caught by the original ASRA Step 4 but not by the max_up_ramp+1 version (n=4)."""
import itertools,collections
from model import *
import asra as R
from fixcheck import verify_asra2
n=4; ases=list(range(n)); pairs=list(itertools.combinations(ases,2)); C=collections.Counter()
for lab in itertools.product([None,'prov','cust','peer'],repeat=len(pairs)):
    rel={}
    for (x,y),r in zip(pairs,lab):
        if r: rel[(x,y)]=r; rel[(y,x)]=INV[r]
    tspas=spas_of(rel,ases)
    tasra={x:{'C':{y for (z,y),r in rel.items() if z==x and r=='cust'},'LP':{y for (z,y),r in rel.items() if z==x and r=='peer'}} for x in ases}
    adj=collections.defaultdict(list)
    for (x,y) in rel: adj[x].append(y)
    for L in range(2,n):
        for path in itertools.permutations(ases,L):
            if any((path[i],path[i+1]) not in rel for i in range(L-1)): continue
            for recv in adj[path[-1]]:
                if recv in path or rel[(recv,path[-1])]!='prov': continue
                if leak_free(rel,path,recv): continue
                for k in range(len(path)+1):
                    for dep in itertools.combinations(path,k):
                        aspa={x:tspas[x] for x in dep}
                        for k2 in range(len(dep)+1):
                            for dep2 in itertools.combinations(dep,k2):
                                asra={x:tasra[x] for x in dep2}
                                for alg in 'AB':
                                    o,s=verify_asra2(aspa,asra,path,True,alg,False)
                                    of,sf=verify_asra2(aspa,asra,path,True,alg,True)
                                    if o=='Invalid' and of!='Invalid':
                                        A=list(path); N=len(A); mu,nu,md,nd=bounds(aspa,A)
                                        # lateral hops that fired in the original range but are below the fixed range
                                        fired=[i for i in range(nu+1,N) if R.lateral(aspa,asra,A[i-1],A[i])]
                                        i=fired[0]
                                        prev=authorized(aspa,A[i-2],A[i-1]) if i>=2 else None
                                        cur=authorized(aspa,A[i-1],A[i])
                                        C[(alg,'i==max_up' if i==mu else 'i<max_up','prev='+str(prev),'cur='+cur)]+=1
for k,v in sorted(C.items()): print(k,v)
