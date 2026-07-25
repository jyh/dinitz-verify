import itertools
V=['s','u','v','w','t1','t2','t3']
# arc: (tail, head, x, c)
A={'st1':('s','t1',10,2),'st2':('s','t2',6,3),'su':('s','u',24,0),
   'ut3':('u','t3',10,2),'uv':('u','v',14,0),'vt1':('v','t1',5,0),
   'vw':('v','w',9,0),'wt2':('w','t2',4,0),'wt3':('w','t3',5,0)}
dem={'t1':15,'t2':10,'t3':15}; D=max(dem.values())
# conservation
for z in V:
    inn=sum(a[2] for a in A.values() if a[1]==z); out=sum(a[2] for a in A.values() if a[0]==z)
    net=out-inn
    exp = sum(dem.values()) if z=='s' else -dem.get(z,0)
    assert net==exp, (z,net,exp)
print("conservation OK; dmax =",D)
print("fractional cost =", sum(a[2]*a[3] for a in A.values()))
# enumerate ALL walks s->t by brute force up to length 8 (well past the rank bound)
def walks(x,y,maxlen=8):
    out=[]
    def go(cur,path):
        if cur==y and path: out.append(tuple(path))
        if len(path)>=maxlen: return
        for n,(t,h,_,_) in A.items():
            if t==cur: go(h,path+[n])
    go(x,[]); return out
P={t:walks('s',t) for t in dem}
for t in P: print(t, P[t])
assert all(len(P[t])==2 for t in P), "path count"
best=None; feasible=0
for c1 in P['t1']:
  for c2 in P['t2']:
    for c3 in P['t3']:
      load={n:0 for n in A}
      for t,p in (('t1',c1),('t2',c2),('t3',c3)):
          for n in set(p): load[n]+=dem[t]
      if all(load[n]<=A[n][2]+D for n in A):
          feasible+=1
          cost=sum(A[n][3]*load[n] for n in A)
          best=cost if best is None else min(best,cost)
print("capacity-good routings:",feasible,"  min unsplittable cost:",best)
