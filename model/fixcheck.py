import itertools,sys,collections
from model import *
import asra as R
def verify_asra2(aspa, asra, path, downstream, alg, fix):
    out = verify(aspa, path, downstream)
    if not downstream or out=='Invalid': return out,0
    A = compress(path); N = len(A); mu,nu,md,nd = bounds(aspa, A)
    if alg=='A':
        if nu == N or nu + nd > N: return out,0
        hi=N-nd
    else:
        if nu == N: return out,0
        hi=N-1
    for i in range(nu, hi+1):
        if 1<=i<N and R.fake_link(aspa,asra,A[i-1],A[i],alg): return 'Invalid',3
    lo = (mu if fix else nu) + 1
    for i in range(lo, hi+1):
        if 1<=i<N and R.lateral(aspa,asra,A[i-1],A[i]): return 'Invalid',4
    return out,0
if __name__=='__main__':
    n=int(sys.argv[1]); ases=list(range(n)); pairs=list(itertools.combinations(ases,2))
    C=collections.Counter()
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
                    truth=leak_free(rel,path,recv)
                    for k in range(len(path)+1):
                        for dep in itertools.combinations(path,k):
                            aspa={x:tspas[x] for x in dep}
                            for k2 in range(len(dep)+1):
                                for dep2 in itertools.combinations(dep,k2):
                                    asra={x:tasra[x] for x in dep2}
                                    base=verify(aspa,path,True)
                                    for alg in 'AB':
                                        for fix in (False,True):
                                            o,step=verify_asra2(aspa,asra,path,True,alg,fix)
                                            tag='%s%s'%(alg,'-fixed' if fix else '')
                                            if o=='Invalid' and truth: C[(tag,'FP step%d'%step)]+=1
                                            if (not truth) and o=='Invalid' and base!='Invalid': C[(tag,'extra leaks caught (step%d)'%step)]+=1
                                            if not truth: C[(tag,'leak cases')]+=1
    for k in sorted(C): print(k,C[k])
