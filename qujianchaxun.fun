val N = getInt() and M = getInt();
val list1 = getIntTable(N);
val a = Array.fromList list1;

val arr = Array2.array(N,N,0);

fun arrnum(arr,a,n) = 
let 
fun new(r:int,c:int) = 
if r = n  then ()
else if c = n then new(r+1,r+1)
else if r = c then let val tmp1 = Array2.update(arr,r,c,Array.sub(a,c)) in new(r,c+1) end
else let val tmp2 = Array2.update(arr,r,c,Int.max(Array2.sub(arr,r,c-1),Array.sub(a,c))) in new(r,c+1) end
in
new(0,0)
end;

fun prians(0,arr) = ()
|prians(M:int,arr) = 
let
val tmp = printInt(Array2.sub(arr,getInt()-1,getInt()-1))
in prians(M-1,arr) end; 
