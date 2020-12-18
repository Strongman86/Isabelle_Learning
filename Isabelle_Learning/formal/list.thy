theory list
imports Main
begin
value "[uminus int(1),int(0),int(1)]"
value "nat(1)#nat(9)#[]"
value "[int(1)..int(10)]"
value "hd [int(1),int(3),int(6)]"
value "tl [int(1),int(3),int(6)]"
value "last [int(1),int(3),int(6)]"
value "length [int(1),int(3),int(6)]"
value "drop 2 [int(1),int(3),int(6)]"
value "rev [int(1),int(3),int(6)]"
value "sum_list [int(1),int(3),int(6)]"
value "sort (rev [int(1),int(7),int(6)])"
value "set [int(1),int(3),int(6)]"
value "(int(1)) \<in> {int(1),int(3),int(6)}"
value "{int(1),int(3),int(6)}\<inter> {int(7),int(3),int(9)}"
value "{int(1),int(3),int(6)}\<union> {int(7),int(3),int(9)}"
value "Pow {int(7),int(3),int(9)}"
value "\<forall>x\<in> {int(7),int(3),int(9)}. x>2"
end