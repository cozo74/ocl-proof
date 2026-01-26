From Stdlib Require Import String ZArith Reals List.


Import ListNotations.


From OCL.equivalence Require Import Models.



Definition var_name := string.


(* ================================= Term ======================================= *)


(* 一元运算 *)
Inductive bool_unop : Type :=
| UNot (* not *).

Inductive arith_unop : Type :=
| UNeg (* -x *) | UAbs | UFloor | URound.

Inductive str_unop : Type :=
| UToUpper | UToLower | USize.




(* 二元运算 *)
Inductive bool_binop : Type :=
| BAnd | BOr | BXor | BImplies.

Inductive comp_binop : Type :=
| BEq | BNe | BLt | BLe | BGt | BGe.

Inductive arith_binop : Type :=
| BAdd | BSub | BMul | BDiv.

Inductive str_binop : Type :=
| BConcat.

Inductive agg_binop : Type :=
| BMax | BMin | BMod | BDivInt.

(* bag聚合函数 *)
Inductive aggop : Type  :=
| AggSize | AggSum 
| AggMin | AggMax 
.




(* OCL 表达式（统一 AST） *)
Inductive tm : Type :=



    (* ======================== Var 表达式 ======================== *)
    | CVar    : var_name -> tm



    (* ======================== operation 表达式 ======================== *)
    (*  无参operation： 字面量构造器  *)
    | CBool   : bool -> tm
    | CInt    : Z -> tm
    | CReal   : R -> tm
    | CString : string -> tm


    (*  basic type 有参operation： 一元操作  *)
    | CBoolUn    : bool_unop -> tm -> tm
    | CArithUn   : arith_unop -> tm -> tm
    | CStrUn     : str_unop -> tm -> tm
    | CSubstring : tm -> Z -> Z -> tm 


    (*  basic type 有参operation： 二元操作  *)
    | CBoolBin    : bool_binop -> tm -> tm -> tm
    | CCompBin    : comp_binop -> tm -> tm -> tm
    | CArithBin    : arith_binop -> tm -> tm -> tm
    | CStrBin    : str_binop -> tm -> tm -> tm
    | CAggBin    : agg_binop -> tm -> tm -> tm



    (*  object type 有参operation： allInstances, 对象属性/角色  *)
    | CAllInstances : class_name -> tm
    | CAttr   : tm -> attr_name -> tm
    | CRole   : tm -> role_name -> tm
    | CNRole   : tm -> role_name -> tm





    (*  Bag type 有参operation： 字面量构造器 *)
    | CBagLiteral : T_b -> list tm -> tm


    (*  Bag type 有参operation： Bag 集合运算  *)
    | CUnion        : tm -> tm -> tm
    (* | CIntersect    : tm -> tm -> tm *)
    | CDifference   : tm -> tm -> tm
    (* | CSymDiff      : tm -> tm -> tm *)





    (*  Bag type 有参operation： Bag 函数 。 可用select+size表示*)
    (* | CIncludesAll  : tm -> tm -> tm *)
    (* | CExcludesAll  : tm -> tm -> tm *)
    (* | CIncludes     : tm -> tm -> tm *)
    (* | CExcludes     : tm -> tm -> tm *)
    (* | CIsEmpty      : tm -> tm *)
    (* | CNotEmpty     : tm -> tm *)
    (* | CIsUnique     : tm -> tm *)
    | CAggregate : aggop -> tm -> tm


    (* ======================== iterator 表达式 ======================== *)
 
    (*  Bag type 有参operation：Iterator。 可用select+size表示*)
    (* | CForAll   : tm -> var_name -> tm -> tm *)
    (* | CExists   : tm -> var_name -> tm -> tm *)
    (* | COne      : tm -> var_name -> tm -> tm *)
    | CSelect   : tm -> var_name -> tm -> tm
    (* | CReject   : tm -> var_name -> tm -> tm *)
    | CCollect  : tm -> attr_name -> tm
    | CRCollect  : tm -> role_name -> tm
    | CNRCollect : tm -> role_name -> tm


    (*  context *)
    (* | CContext : class_name -> tm -> tm *)

.
