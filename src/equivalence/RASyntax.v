From Stdlib Require Import String ZArith Reals List.
Import ListNotations.


From OCL.equivalence Require Import Models.
From OCL.equivalence Require Import OCLSyntax.
Open Scope string_scope.
(*************************************************************)
(*  Relational Algebra (RA) Syntax                            *)
(*                                                           *)
(*  设计原则（对齐 Apache Calcite）：                         *)
(*  - RA      ：关系级算子（RelNode）                         *)
(*  - RAExpr  ：行级表达式（RexNode / 条件 / 标量表达式）     *)
(*  - 所有 RAExpr 都在单行 Row 上求值                         *)
(*  - 所有 RA 都在 DBInstance 上求值，返回 TableInst          *)
(*************************************************************)

From Stdlib Require Import String List.
Import ListNotations.

(* 表名、列名 *)
Definition TableName := string.
Definition ColName   := string.






(*************************************************************)
(*  RexNode : Row-level scalar / condition expressions       *)
(*                                                           *)
(*  对齐 Apache Calcite RexNode                              *)
(*  - 在单行 Row 上求值                                     *)
(*  - 用于 σ / π / ⋈                                        *)
(*************************************************************)

Inductive ra_rex : Type :=

(* 基本项 *)
| RCol   : ColName -> ra_rex          (* 读取当前行的列 *)
| RVal   : value -> ra_rex            (* 常量 *)

(* 一元运算 *)
| RBoolUn  : bool_unop  -> ra_rex -> ra_rex
| RArithUn : arith_unop -> ra_rex -> ra_rex
| RStrUn   : str_unop   -> ra_rex -> ra_rex

(* 二元运算 *)
| RBoolBin  : bool_binop  -> ra_rex -> ra_rex -> ra_rex
| RComp     : comp_binop  -> ra_rex -> ra_rex -> ra_rex
| RArithBin : arith_binop -> ra_rex -> ra_rex -> ra_rex
| RStrBin   : str_binop   -> ra_rex -> ra_rex -> ra_rex
| RAggBin   : agg_binop   -> ra_rex -> ra_rex -> ra_rex

(* String ops with integer arguments *)
| RAt        : ra_rex -> Z -> ra_rex
| RSubstring : ra_rex -> Z -> Z -> ra_rex.




(*************************************************************)
(*  Projection item                                          *)
(*                                                           *)
(*  Calcite:                                                 *)
(*    SELECT expr AS name                                    *)
(*************************************************************)

Record RAProjItem : Type := {
  proj_expr : ra_rex;   (* 列表达式 *)
  proj_name : ColName   (* 输出列名 *)
}.


(*************************************************************)
(*  Relational Algebra operators (Calcite: RelNode)          *)
(*                                                           *)
(*  每个构造子对应一个逻辑关系算子                           *)
(*************************************************************)

Inductive ra_rel : Type :=

(* 空关系 *)
| RAEmpty : ra_rel

(* 常量关系 (single bag) *)
| RAValues : list value -> ra_rel

(* 表扫描 *)
| RATable  : TableName -> ra_rel
(* 语义：直接从 TableSchema 中读取该表 *)


(* 从TableSchema构建一个表 *)
| RATableSchema : TableSchema -> ra_rel


(* 选择 σ *)
| RASelect : ra_rex -> ra_rel -> ra_rel
(* 语义：保留满足条件的行 *)

(* 投影 π *)
| RAProject : list RAProjItem -> ra_rel -> ra_rel
(* 语义：对每一行计算新列并生成新 schema *)

(* 内连接 ⋈ *)
| RAJoin   : ra_rex -> ra_rel -> ra_rel -> ra_rel
(* 语义：笛卡尔积 + 条件过滤（inner join） *)

(* 并、差（Bag 语义） *)
| RAUnion  : ra_rel -> ra_rel -> ra_rel
| RAIntersect  : ra_rel -> ra_rel -> ra_rel
| RADiff   : ra_rel -> ra_rel -> ra_rel

(* 去重（可选，用于 IsUnique / 集合语义） *)
| RADistinct : ra_rel -> ra_rel

(* 分组与聚合 γ *)
| RAAggregate :
    list ColName ->                      (* group by 列 *)
    list (ColName * aggop * ColName) ->  (* newCol := agg(op, col) *)
    ra_rel -> ra_rel.

