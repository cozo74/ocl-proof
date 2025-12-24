From Stdlib Require Import String ZArith Reals List.

From OCL Require Import Types Utils.
Import ListNotations.




(* ================================= Term ======================================= *)

Definition var  := string.
Definition attr := string.
Definition role := string.
Definition nrole := string.
Definition class := string.

(* 一元运算 *)
Inductive bool_unop : Type :=
| UNot (* not *).

Inductive arith_unop : Type :=
| UNeg (* -x *) | UAbs | UFloor | URound.

Inductive str_unop : Type :=
| UToUpper | UToLower.




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

(* 集合聚合函数 *)
Inductive aggop : Type  :=
| AggMin | AggMax | AggSize | AggSum.

(* 暂不考虑 AggAvg，可通过sum和size的组合实现.  *)



(* OCL 表达式（统一 AST） *)
Inductive tm : Type :=


(*  字面量  *)
| CBool   : bool -> tm
| CInt    : Z -> tm
| CReal   : R -> tm
| CString : string -> tm
| CObject : string -> tm



(*  集合（Bag） *)
| CEmptyBag   : ty -> tm
| CBagLiteral : list tm -> tm



(*  context *)
| CContext : string -> tm -> tm



(*  Var Self  *)
| CVar    : var -> tm
| CSelf   : tm


(*  对象 / 属性 / 角色  *)
| CAttr   : tm -> attr -> tm
| CRole   : tm -> role -> tm
| CNRole   : tm -> nrole -> tm


(*  allInstances  *)
| CAllInstances : class -> tm


(*  一元操作  *)
| CBoolUn    : bool_unop -> tm -> tm
| CArithUn   : arith_unop -> tm -> tm
| CStrUn     : str_unop -> tm -> tm

(*  二元操作  *)
| CBoolBin    : bool_binop -> tm -> tm -> tm
| CCompBin    : comp_binop -> tm -> tm -> tm
| CArithBin    : arith_binop -> tm -> tm -> tm
| CStrBin    : str_binop -> tm -> tm -> tm
| CAggBin    : agg_binop -> tm -> tm -> tm




(*  Bag 运算  *)
| CUnion        : tm -> tm -> tm
| CIntersect    : tm -> tm -> tm
| CDifference   : tm -> tm -> tm
| CSymDiff      : tm -> tm -> tm



(*  Bag 谓词  *)
| CIncludesAll  : tm -> tm -> tm
| CExcludesAll  : tm -> tm -> tm
| CIncludes     : tm -> tm -> tm
| CExcludes     : tm -> tm -> tm
| CIsEmpty      : tm -> tm
| CNotEmpty     : tm -> tm
| CIsUnique     : tm -> tm

(*  Iterator（绑定变量！）, forall，exists中的varList是语法糖，可脱糖为单变量表示 *)

| CForAll   : tm -> var -> tm -> tm
| CExists   : tm -> var -> tm -> tm
| CSelect   : tm -> var -> tm -> tm
| CReject   : tm -> var -> tm -> tm
| COne      : tm -> var -> tm -> tm
| CCollect  : tm -> attr -> tm
| CRCollect  : tm -> role -> tm
| CNRCollect : tm -> nrole -> tm


(*  bag聚合  *)
| EAggregate : aggop -> tm -> tm


(* String ops with integer arguments *)
| EAt        : tm -> Z -> tm 
| ESubstring : tm -> Z -> Z -> tm .
