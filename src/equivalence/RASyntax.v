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
(*  Projection item                                          *)
(*                                                           *)
(*  Calcite:                                                 *)
(*    SELECT expr AS name                                    *)
(*************************************************************)

Inductive rel : Type :=
    (* 空关系 *)
    | RAEmpty : rel

    (* 常量关系 (single bag) *)
    | RABagLiteral : T_ra -> list I_ra -> rel


    (* 表扫描 *)
    | RATable  : TableName -> rel
    (* 语义：直接从 TableSchema 中读取该表 *)

    (* 选择 σ *)
    | RASelect : rex -> rel -> rel
    (* 语义：保留满足条件的行 *)

    (* 投影 π           输出列名  列表达式  *)
    | RAProject : list (ColName * rex) -> rel -> rel
    (* 语义：对每一行计算新列并生成新 schema. 可实现重命名、列顺序调整、列之间一元二元操作 *)

    (* 笛卡尔积 *)
    | RACartesian : rel -> rel -> rel


    (* 内连接 ⋈ *)
    | RAJoin   : rex -> rel -> rel -> rel
    (* 语义：笛卡尔积 + 条件过滤（inner join） *)

    (* 并、差（Bag 语义） *)
    | RAUnion  : rel -> rel -> rel
    (* | RAIntersect  : rel -> rel -> rel *)
    | RADiff   : rel -> rel -> rel

    (* 去重（可选，用于 IsUnique / 集合语义） *)
    | RADistinct : rel -> rel


    (* 分组与聚合 γ *)
    | RAAggregate :
        list ColName ->                      (* group by 列 *)
        list (ColName * aggop * ColName) ->  (* newCol := agg(op, col) *)
        rel -> rel



  (*************************************************************)
  (*  RexNode : Row-level scalar / condition expressions       *)
  (*                                                           *)
  (*  对齐 Apache Calcite RexNode                              *)
  (*  - 在单行 Row 上求值                                     *)
  (*  - 用于 σ / π / ⋈                                        *)
  (*************************************************************)

  with rex : Type :=
    (* 基本项 *)
    | RCol : ColName -> rex  (* 读取当前行的列 *)
    | RLit : I_ra -> rex   (* 常量 *)

    (* 一元运算 *)
    | RUnop : unop -> rex -> rex

    (* 二元运算 *)
    | RBinop : binop -> rex -> rex -> rex


    | RSubquery : (ColName * aggop) -> rel -> rex .







(* Record RAProjItem : Type := {
    proj_name : ColName;   (* 输出列名 *)
    proj_expr : rex   (* 列表达式 *)

}. *)


(* Definition mkProj (name : ColName) (e : rex) : RAProjItem :=
  {| proj_name := name; proj_expr := e |}. *)


(* Definition projCol (c : ColName) : RAProjItem :=
  mkProj c (RCol c). *)

Definition mkProj (name : ColName) (e : rex) : ColName * rex :=
  ( name, e ).


Definition projCol (c : ColName) :  ColName * rex :=
  mkProj c (RCol c).




Fixpoint lookup_table_schema
  (LT : list TableSchema) (t : TableName) : option TableSchema :=
  match LT with
  | [] => None
  | ts :: LT' =>
      if String.eqb ts.(table_name) t
      then Some ts
      else lookup_table_schema LT' t
  end.


