fun append([],ys) = ys
  | append(x::xs,ys) = x::append(xs,ys);

fun quicksort([]) = []
    |quicksort(x::[]) = x::[]
    |quicksort(x::xs) = 
let fun partition(left,right,[]):int list=
           append(quicksort(left),x::quicksort(right))
	   |partition(left,right,y::ys)=
	       if(y<=x) then partition(y::left,right,ys)
		   else partition(left,y::right,ys)
		in partition([],[],xs)
end;

val N = getInt();
val List = getIntTable(N);
printIntTable(quicksort(List));