From Stdlib Require Import String ZArith Reals List.


Import ListNotations.


From OCL.equivalence Require Import Models.



Definition var_name := string.



(* =====================   unary, binary operatior  ======================= *)





(* 一元运算 *)
Inductive bool_unop : Type :=
| UNot (* not *).

Inductive arith_unop : Type :=
| UNeg (* -x *) | UAbs | UFloor | URound.

Inductive str_unop : Type :=
| UToUpper | UToLower | USize.


Inductive unop : Type :=
    | U_Bool  : bool_unop  -> unop
    | U_Arith : arith_unop -> unop
    | U_Str   : str_unop   -> unop.

    
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



Inductive binop : Type :=
    | B_Bool  : bool_binop  -> binop
    | B_Comp  : comp_binop  -> binop
    | B_Arith : arith_binop -> binop
    | B_Str   : str_binop   -> binop
    | B_Agg   : agg_binop   -> binop.


(* ================================= Term ======================================= *)





(* OCL 表达式（统一 AST） *)
Inductive tm : Type :=

    (* ======================== Var 表达式 ======================== *)
    | CVar    : var_name -> tm

    (* ======================== operation 表达式 ======================== *)
    (*  无参operation： 字面量构造器  *)
    | CLit    : I_b -> tm

    (*  basic type 有参operation： 一元操作  *)
    | CUnop     : unop -> tm -> tm

    (*  basic type 有参operation： 二元操作 (和object type eq)  *)
    | CBinop    : binop -> tm -> tm -> tm

    (*  object type 有参operation： allInstances, 对象属性/角色  *)
    | CAllInstances : class_name -> tm
    | CAttr   : tm -> attr_name -> tm
    | CRole   : tm -> role_name -> tm
    | CNRole   : tm -> role_name -> tm

    (*  Bag type 有参operation： 字面量构造器 *)
    | CBagLiteral : T_b -> list I_b -> tm

    (*  Bag type 有参operation： Bag 集合运算  *)
    | CUnion        : tm -> tm -> tm
    | CDifference   : tm -> tm -> tm


    (*  Bag type 有参operation： Bag 函数 。 可用select+size表示*)
    | CAggregate : aggop -> tm -> tm

    (* ======================== iterator 表达式 ======================== *)
 
    (*  Bag type 有参operation：Iterator。 可用select+size表示*)
    | CSelect   : tm -> var_name -> tm -> tm


.
