val v = getInt() and e = getInt() and s = getInt();
val edges = Array2.array(v,v,99999999);
fun prinum (arr,0) = ()
|prinum(arr,m) = 
let val v1 = getInt();  
val v2 = getInt();
val edge = getInt();
val tmp1 = Array2.update(arr,v1-1,v2-1,edge);
val tmp2 = Array2.update(arr,v2-1,v1-1,edge);
in prinum(arr,m-1) end;
val minlen = Array.array(v,~1);
Array.update(minlen,s-1,0);
(*x:已走节点,初始为s-1*)
fun minlength(arr,minlen:int array,x:int list,n:int) =
let
val (v,f,l) = 
let 
fun f1 ([],min:int,v:int,fu:int) = (v,fu,min)
|f1 (x::xs:(int*int*int) list,min,v,fu) = if (# 3 x < min) then f1(xs,# 3 x,# 1 x,# 2 x) 
else f1(xs,min,v,fu)

fun getminrow(r) =
let fun new(c,v,min) = 
if c = n then (v,r,min)
else if min>Array2.sub(arr,r,c) then new(c+1,c,Array2.sub(arr,r,c))
else new(c+1,v,min)
in
new(r,r,99999999) end
in
f1(map getminrow x,99999998,n+1,n+1)
end

in
if(v = n + 1) then ()
else let val tmp = Array.update(minlen,v,l + Array.sub(minlen,f)) in minlength(arr,minlen,v::x,n) end
end;

fun prilen(a:int array,n:int) = 
let fun pri n = ()
|pri(i:int) = let val tmp = printInt(Array.sub(a,i)) in pri(i+1) end
in
pri 0
end;


(********************************************************************************)
(*求出该无向图中源点到各点的最短路径，属于Dijstra算法*)
(*对于需高度并行，上面的算法显然是串行的，注意tabulate是可以并行的*)

val n = getInt() and m = getInt() and s = getInt();
val inf = 99999999;
(*仍然使用邻接矩阵来储存图*)
val edges = Array2.array(n,n,inf);
List.tabulate(n,fn x=> Array2.update(edges,x,x,0));
fun readin _ = 
let val v1 = getInt() - 1 and v2 = getInt() - 1 and d = getInt() 
val t1 = Array2.update(edges,v1,v2,Int.min(Array2.sub(edges,v1,v2),d)) and t2 = Array2.update(edges,v2,v1,Int.min(Array2.sub(edges,v2,v1),d)
in () end;
List.tabulate(m,readin);

val dis = Array.array(n,inf);(*结果序列*)
List.tabulate(n,fn x=> Array.update(dis,x,Array2.sub(edges,s,x)));(*初始化*)
val vis = Array.array(n,false);(*标记有无访问*)
fun f _ = 
(*找到dis中最小的，并标记已走*)
let val (v,l) = Array.foldli
(fn (i,x,(u,m))=>if Array.sub(vis,i) = false andalso x < m then (i,x) else (u,m)) 
(s,inf) dis
in if l < inf then let val t1 = Array.update(vis,v,true) (*标记v已走*)
val vi = List.tabulate(n,fn x=> x)
val t2 = map 
(fn x=>if l + Array2.sub(edges,v,x) < Array.sub(dis,x) then Array.update(dis,x,l + Array2.sub(edges,v,x)) else ()) vi
in 0 end   (*更新dis序列中包括v节点在内的值*)
else 0 
end;
List.tabulate(n,f); (*做n次，没有太多并行的意味*)
Array.foldl (fn(x,_)=> if x = inf then printInt(~1) else printInt(x)) () dis;