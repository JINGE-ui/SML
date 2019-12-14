fun clear0 []  = []
|clear0 l = if hd l = 0 then clear0 (tl l) else l;
val n1 = getInt();
val a = Array.fromList(clear0(getIntTable(n1)));
val N1 = Array.length a;
val n2 = getInt();
val list = clear0(getIntTable(n2));
val b = Array.fromList(List.tabulate(N1 - List.length(list),fn x=>0)@list);
val arr = Array.tabulate(N1,fn x=>x);

val arr1 = Array.array(N1+1,0);
val c = Array.foldr (fn (i,c)=> let val tmp = Array.update(arr1,i+1,(Array.sub(a,i)+Array.sub(b,i)+c) mod 10) in 
    (Array.sub(a,i)+Array.sub(b,i)+c)div 10 end) 0 arr;  
Array.update(arr1,0,c);
if Array.foldl (fn (x,max)=>Int.max(x,max)) 0 arr1 = 0 
then let val t1 = printInt(0) in 0 end else
Array.foldli (fn (i,x,vis)=>if x = 0 andalso vis = 1 then 1 else let val tmp = printInt(x) in 0 end) 
1 arr1;
print("\n");

val arr2 = Array.array(N1,0);
Array.foldr (fn (i,c)=> if Array.sub(a,i)-Array.sub(b,i)-c >= 0 then 
let val t1 = Array.update(arr2,i,Array.sub(a,i)-Array.sub(b,i)-c) in 0 end
else let val t2 = Array.update(arr2,i,Array.sub(a,i)-Array.sub(b,i)-c+10) in 1 end )
0 arr;
if Array.foldl (fn (x,max)=>Int.max(x,max)) 0 arr2 = 0 
then let val t1 = printInt(0) in 0 end else
Array.foldli (fn (i,x,vis)=>if x = 0 andalso vis = 1
then 1 else let val tmp = printInt(x) in 0 end) 
1 arr2;
print("\n");

val arr3 = Array.array(2*N1,0);
fun mul1 (j,_) = let
val c = Array.foldri (fn(i,x,c)=> let val d = Array.sub(arr3,i+j+1) + x * Array.sub(b,j) + c 
val tmp = Array.update(arr3,i+j+1,d mod 10) in d div 10 end) 0 a;
val tmp1 = Array.update(arr3,j,c);
in 0 end;
Array.foldr (mul1) 0 arr;
if Array.foldl (fn (x,max)=>Int.max(x,max)) 0 arr3 = 0 
then let val t1 = printInt(0) in 0 end else
Array.foldli (fn (i,x,vis)=>if x = 0 andalso vis = 1 andalso i <> Array.length(arr3) - 1 
then 1 else let val tmp = printInt(x) in 0 end) 
1 arr3;

