val n = getInt() and m = getInt() and s = getInt();
val inf = 99999999;
val edges = Array2.array(n,n,inf);
List.tabulate(n,fn x=> Array2.update(edges,x,x,0));
fun readin _ = 
let val v1 = getInt() - 1 and v2 = getInt() - 1 and d = getInt() 
val t1 = Array2.update(edges,v1,v2,Int.min(Array2.sub(edges,v1,v2),d)) and t2 = Array2.update(edges,v2,v1,Int.min(Array2.sub(edges,v2,v1),d)
in () end;
List.tabulate(m,readin);
val dis = Array.array(n,inf);
List.tabulate(n,fn x=> Array.update(dis,x,Array2.sub(edges,s,x)));
val vis = Array.array(n,false);
fun f _ = 
(*找到dis中最小的，并标记已走*)
let val (v,l) = Array.foldli
(fn (i,x,(u,m))=>if Array.sub(vis,i) = false andalso x < m then (i,x) else (u,m)) 
(s,inf) dis
in if l < inf then let val t1 = Array.update(vis,v,true)) 
val vi = List.tabulate(n,fn x=> x)
val t2 = map 
(fn x=>if l + Array2.sub(edges,v,x) < Array.sub(dis,x) then Array.update(dis,x,l + Array2.sub(edges,v,x)) else ()) vi
in 0 end 
else 0 
end;
List.tabulate(n,f);
Array.foldl (fn(x,_)=> if x = inf then printInt(~1) else printInt(x)) () dis;