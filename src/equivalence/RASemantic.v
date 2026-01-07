(*************************************************************)
(*                                                           *)
(*        Relational Algebra Semantics (Big-step)             *)
(*                                                           *)
(*  Design principles:                                       *)
(*  - RexNode: row-level, pure, no DB access                 *)
(*  - ra_rel  : relation-level, evaluated over DBInstance     *)
(*  - No subQuery in syntax: all subqueries are eliminated   *)
(*    by rewriting into joins / aggregates before semantics  *)
(*                                                           *)
(*************************************************************)

From Stdlib Require Import
  String
  List
  Bool
  ZArith
  Reals.

Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import OCLSemantic OCLSyntax.
From OCL.equivalence Require Import RASyntax Models.




(*************************************************************)
(*                 Row-level semantics                       *)
(*                RexNode evaluation                         *)
(*************************************************************)

(* RexNode evaluation is:
     - row-local
     - pure
     - total up to option failure
*)

Inductive evalRexR : Row -> ra_rex -> value -> Prop :=

| ER_Col :
    forall r c v,
      r.(r_get) c = Some v ->
      evalRexR r (RCol c) v

| ER_Val :
    forall r v,
      evalRexR r (RVal v) v

| ER_BoolUn :
    forall r op e1 v1 v,
      evalRexR r e1 v1 ->
      bool_unop_sem op v1 = Some v ->
      evalRexR r (RBoolUn op e1) v

| ER_ArithUn :
    forall r op e1 v1 v,
      evalRexR r e1 v1 ->
      arith_unop_sem op v1 = Some v ->
      evalRexR r (RArithUn op e1) v

| ER_StrUn :
    forall r op e1 v1 v,
      evalRexR r e1 v1 ->
      str_unop_sem op v1 = Some v ->
      evalRexR r (RStrUn op e1) v

| ER_BoolBin :
    forall r op e1 e2 v1 v2 v,
      evalRexR r e1 (V_Bool v1) ->
      evalRexR r e2 (V_Bool v2) ->
      bool_binop_sem op v1 v2 = v ->
      evalRexR r (RBoolBin op e1 e2) (V_Bool v)

| ER_Comp :
    forall r op e1 e2 v1 v2 v,
      evalRexR r e1 v1 ->
      evalRexR r e2 v2 ->
      comp_binop_sem op v1 v2 = Some v ->
      evalRexR r (RComp op e1 e2) (V_Bool v)

| ER_ArithBin :
    forall r op e1 e2 v1 v2 v,
      evalRexR r e1 v1 ->
      evalRexR r e2 v2 ->
      arith_binop_sem op v1 v2 = Some v ->
      evalRexR r (RArithBin op e1 e2) v

| ER_StrBin :
    forall r op e1 e2 v1 v2 v,
      evalRexR r e1 v1 ->
      evalRexR r e2 v2 ->
      str_binop_sem op v1 v2 = Some v ->
      evalRexR r (RStrBin op e1 e2) v

| ER_AggBin :
    forall r op e1 e2 v1 v2 v,
      evalRexR r e1 v1 ->
      evalRexR r e2 v2 ->
      agg_binop_sem op v1 v2 = Some v ->
      evalRexR r (RAggBin op e1 e2) v

(* ------------------- String At ------------------- *)
| ER_At :
    forall row rex s i r,
      evalRexR row rex (V_String s) ->
      StringAt s i r ->
      evalRexR row (RAt rex i) (V_String r)

| ER_Substring :
    forall row rex s i j r,
      evalRexR row rex (V_String s) ->
      StringSub s i j r ->
      evalRexR row (RSubstring rex i j) (V_String r).
  
  







(*************************************************************)
(*                  Row construction helpers                 *)
(*************************************************************)

(* Merge two rows (used by join).
   Schema disjointness is guaranteed by typing. *)
Definition row_merge (r1 r2 : Row) : Row :=
  {|
    r_schema := List.app r1.(r_schema) r2.(r_schema);
    r_get :=
      fun c =>
        match r1.(r_get) c with
        | Some v => Some v
        | None   => r2.(r_get) c
        end
  |}.


Definition project_schema (ps : list RAProjItem) : RowSchema :=
map proj_name ps.

Inductive project_rowR
  (ps : list RAProjItem)
  (r  : Row)
  : Row -> Prop :=

| ProjectRowR :
    forall r',
      (* schema 正确 *)
      r'.(r_schema) = project_schema ps ->

      (* 每一个投影列都能由 RexNode 求值得到 *)
      (forall p v,
         In p ps ->
         evalRexR r (proj_expr p) v ->
         r'.(r_get) (proj_name p) = Some v) ->

      (* 非投影列不可访问 *)
      (forall c,
         ~ In c (project_schema ps) ->
         r'.(r_get) c = None) ->

      project_rowR ps r r'.


(* 认为row是可以判断是否相等的，但不讨论判等的具体逻辑  *)
Parameter row_eq_dec : forall (r1 r2 : Row), {r1 = r2} + {r1 <> r2}.


Fixpoint bag_diff_rows (xs ys : list Row) : list Row :=
  match xs with
  | [] => []
  | x :: xs' =>
      if in_dec row_eq_dec x ys then
        bag_diff_rows xs' ys
      else
        x :: bag_diff_rows xs' ys
  end.


Fixpoint remove_dup_rows (xs : list Row) : list Row :=
  match xs with
  | [] => []
  | x :: xs' =>
      if in_dec row_eq_dec x xs' then
        remove_dup_rows xs'
      else
        x :: remove_dup_rows xs'
  end.



Definition group_key (gcols : list ColName) (r : Row)
  : list (option value) :=
  map (fun c => r.(r_get) c) gcols.


(* 认为value是可以判断是否相等的，但不讨论判等的具体逻辑  *)
Parameter value_eq_dec :
  forall (v1 v2 : value), {v1 = v2} + {v1 <> v2}.


Definition option_value_eq_dec
  (o1 o2 : option value)
  : {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
  apply value_eq_dec.
Defined.

Definition list_option_value_eq_dec
  (xs ys : list (option value))
  : {xs = ys} + {xs <> ys}.
Proof.
  decide equality.
  apply option_value_eq_dec.
Defined.


(* Definition same_group
  (gcols : list ColName) (r1 r2 : Row) : Prop :=
  group_key gcols r1 = group_key gcols r2. *)



Fixpoint insert_group
  (gcols : list ColName)
  (r : Row)
  (groups : list (list Row))
  : list (list Row) :=
  match groups with
  | [] => [[r]]
  | grp :: rest =>
      match grp with
      | [] => grp :: insert_group gcols r rest
      | r' :: _ =>
          if list_option_value_eq_dec
               (group_key gcols r)
               (group_key gcols r')
          then (r :: grp) :: rest
          else grp :: insert_group gcols r rest
      end
  end.




Fixpoint group_by
  (gcols : list ColName)
  (rows : list Row)
  : list (list Row) :=
  match rows with
  | [] => []
  | r :: rs =>
      insert_group gcols r (group_by gcols rs)
  end.


Definition group_key_value
  (grp : list Row)
  (c   : ColName)
  : option value :=
  match grp with
  | [] =>
      (* should not happen for well-formed groups *)
      None
  | r :: _ =>
      r.(r_get) c
  end.


(* OCLSemantic.v 中的aggop_sem *)
Definition agg_sem := aggop_sem.



Fixpoint collect_col
  (grp : list Row)
  (col : ColName)
  : list value :=
  match grp with
  | [] => []
  | r :: rs =>
      match r.(r_get) col with
      | Some v => v :: collect_col rs col
      | None   => collect_col rs col
      end
  end.


(* 
  在一个分组 grp 中，计算聚合后得到的列 c 的值。
  如果 c 不是一个聚合产生的列，返回 None；
  如果是，就按照聚合定义真正算出它的值。
*)
Definition eval_agg
  (grp  : list Row)
  (c    : ColName)
  (aggs : list (ColName * aggop * ColName))
  : option value :=
  match find
          (fun '(newc, _, _) => String.eqb newc c)
          aggs
  with
  | None =>
      (* c is not an aggregated column *)
      None
  | Some (_, op, srcCol) =>
      (* apply aggregation operator to source column values *)
      agg_sem op (collect_col grp srcCol)
  end.



Definition values_row (v : value) : Row :=
  {|
    r_schema := ["elem"];
    r_get :=
      fun c =>
        if String.eqb c "elem"
        then Some v
        else None
  |}.




(*************************************************************)
(* 笛卡尔积中的行合并关系                                   *)
(*                                                           *)
(*  r' 是由 r1 与 r2 通过 row_merge 得到的行                 *)
(*************************************************************)
Inductive cartesian_rowR : Row -> Row -> Row -> Prop :=
| CartesianRow_intro :
    forall r1 r2,
      cartesian_rowR r1 r2 (row_merge r1 r2).








(*************************************************************)
(*                                                           *)
(*      Relational Algebra Big-step Semantics (Relation)     *)
(*                                                           *)
(*  evalRAR db q rows                                        *)
(*    = 在数据库 db 上，RA 查询 q 成功求值，                 *)
(*      得到结果表 rows                                     *)
(*                                                           *)
(*  说明：                                                   *)
(*  - 这是“成功语义”（success semantics）                   *)
(*  - 所有失败情况 = 该关系不可证                           *)
(*  - RexNode 的求值通过 evalRexR（关系）完成                *)
(*                                                           *)
(*************************************************************)

Inductive evalRAR : DBInstance -> ra_rel -> TableInst -> Prop :=


| ER_Empty :
    forall db,
      evalRAR db RAEmpty []


| ER_Values :
    forall db vs,
      evalRAR db (RAValues vs)
        (map (fun v => values_row v) vs)





(*************************************************************)
(* 表扫描：RATable                                           *)
(*                                                           *)
(*  如果数据库中存在表 t，其内容为 rows，                    *)
(*  那么 RATable t 的求值结果就是 rows                       *)
(*************************************************************)
| ER_Table :
    forall db t rows,
      db.(tables) t = Some rows ->
      evalRAR db (RATable t) rows


| ER_TableSchema :
    forall db ts rows,
      db.(tables) ts.(table_name) = Some rows ->
      evalRAR db (RATableSchema ts) rows


(*************************************************************)
(* 选择：RASelect                                            *)
(*                                                           *)
(*  rows' 恰好是 rows 中所有满足：                           *)
(*    - cond 在该行上可成功求值                              *)
(*    - 且结果为 true                                        *)
(*  的行组成的表                                             *)
(*************************************************************)
| ER_Select :
    forall db cond q rows rows',
      evalRAR db q rows ->

      (* rows' ⊆ rows：所有被保留的行都来自原表 *)
      (forall r,
         In r rows' ->
         In r rows) ->

      (* rows 中满足条件的行一定出现在 rows' 中 *)
      (forall r,
         In r rows ->
         (exists v, evalRexR r cond v /\ v = V_Bool true) ->
         In r rows') ->

      evalRAR db (RASelect cond q) rows'


(*************************************************************)
(* 投影：RAProject                                          *)
(*                                                           *)
(*  对输入表中的每一行 r，                                   *)
(*  根据投影列表 ps 构造一行 r'                              *)
(*  project_rowR 描述“r 在 ps 下的投影结果”                 *)
(*************************************************************)
| ER_Project :
    forall db ps q rows rows',
      evalRAR db q rows ->

      (* 每一个输入行 r 都能投影成某个输出行 r' *)
      (forall r,
         In r rows ->
         exists r',
           project_rowR ps r r' /\
           In r' rows') ->

      (* 每一个输出行 r' 都来自某个输入行的投影 *)
      (forall r',
         In r' rows' ->
         exists r,
           In r rows /\
           project_rowR ps r r') ->

      evalRAR db (RAProject ps q) rows'



(*************************************************************)
(* 笛卡尔积：RACartesian                                     *)
(*                                                           *)
(*  对输入表 rows1 与 rows2，输出所有 r1++r2                  *)
(*  cartesian_rowR 描述“(r1,r2) 生成输出行 r'”                *)
(*************************************************************)
| ER_Cartesian :
    forall db q1 q2 rows1 rows2 rows',
      evalRAR db q1 rows1 ->
      evalRAR db q2 rows2 ->

      (* 每一个输入对 (r1,r2) 都能生成某个输出行 r' *)
      (forall r1 r2,
         In r1 rows1 ->
         In r2 rows2 ->
         exists r',
           cartesian_rowR r1 r2 r' /\
           In r' rows') ->

      (* 每一个输出行 r' 都来自某个输入对 (r1,r2) *)
      (forall r',
         In r' rows' ->
         exists r1 r2,
           In r1 rows1 /\
           In r2 rows2 /\
           cartesian_rowR r1 r2 r') ->

      evalRAR db (RACartesian q1 q2) rows'


(*************************************************************)
(* 连接：RAJoin                                             *)
(*                                                           *)
(*  rows' 恰好是：                                           *)
(*    - 从 rows1 × rows2 中                                 *)
(*    - 合并行 row_merge r1 r2                               *)
(*    - 且 join 条件在合并行上求值为 true                   *)
(*  得到的所有结果行                                        *)
(*************************************************************)
| ER_Join :
    forall db cond q1 q2 rows1 rows2 rows',
      evalRAR db q1 rows1 ->
      evalRAR db q2 rows2 ->

      (* rows' 中的每一行都来自合法的 join *)
      (forall r,
         In r rows' ->
         exists r1 r2 v,
           In r1 rows1 /\
           In r2 rows2 /\
           r = row_merge r1 r2 /\
           evalRexR r cond v /\
           v = V_Bool true) ->

      (* 所有满足 join 条件的合并行都出现在 rows' 中 *)
      (forall r1 r2 v,
         In r1 rows1 ->
         In r2 rows2 ->
         evalRexR (row_merge r1 r2) cond v ->
         v = V_Bool true ->
         In (row_merge r1 r2) rows') ->

      evalRAR db (RAJoin cond q1 q2) rows'


(*************************************************************)
(* 并：RAUnion                                              *)
(*                                                           *)
(*  Bag 语义：直接连接两个结果表                            *)
(*************************************************************)
| ER_Union :
    forall db q1 q2 rows1 rows2,
      evalRAR db q1 rows1 ->
      evalRAR db q2 rows2 ->
      evalRAR db (RAUnion q1 q2) (List.app rows1 rows2)

(*************************************************************)
(* 交：RAIntersect                                          *)
(*                                                           *)
(*  集合语义（Set-style）：                                 *)
(*  A ∩ B ≜ A \ (A \ B)                                     *)
(*************************************************************)

| ER_Intersect :
    forall db q1 q2 rows,
      schema_of db.(schema) q1 = schema_of db.(schema) q2 ->
      schema_of db.(schema) q1 <> [] ->
      evalRAR db (RADiff q1 (RADiff q1 q2)) rows ->
      evalRAR db (RAIntersect q1 q2) rows




(*************************************************************)
(* 差：RADiff                                               *)
(*                                                           *)
(*  使用 bag 差集语义                                       *)
(*************************************************************)
(* | ER_Diff :
    forall db q1 q2 rows1 rows2 rows',
      evalRAR db q1 rows1 ->
      evalRAR db q2 rows2 ->
      bag_diff_rows rows1 rows2 = rows' ->
      evalRAR db (RADiff q1 q2) rows' *)

| ER_Diff_SameSchema :
    forall db q1 q2 rows1 rows2 rows',
      schema_of db.(schema) q1 = schema_of db.(schema) q2 ->
      evalRAR db q1 rows1 ->
      evalRAR db q2 rows2 ->
      bag_diff_rows rows1 rows2 = rows' ->
      evalRAR db (RADiff q1 q2) rows'


| ER_Diff_EmptySchema :
    forall db q1 q2 rows1 rows2 rows',
      schema_of db.(schema) q2 = [] ->
      evalRAR db q1 rows1 ->
      evalRAR db q2 rows2 ->
      rows' =
        match rows2 with
        | [] => rows1
        | _  => []
        end ->
      evalRAR db (RADiff q1 q2) rows'


(*************************************************************)
(* 去重：RADistinct                                         *)
(*                                                           *)
(*  移除表中的重复行                                        *)
(*************************************************************)
| ER_Distinct :
    forall db q rows rows',
      evalRAR db q rows ->
      remove_dup_rows rows = rows' ->
      evalRAR db (RADistinct q) rows'


(*************************************************************)
(* 聚合：RAAggregate                                        *)
(*                                                           *)
(*  1. 先对输入表 rows 按 gcols 分组                        *)
(*  2. 每个分组生成一行：                                   *) 
(*     - group by 列直接取 key                              *)
(*     - 聚合列由 eval_agg 计算                             *)
(*************************************************************)


(* Invariant:
   - RAAggregate always produces one row per group
   - group_by [] rows = [rows]
   - Aggregate results are set-like (no duplicates)
   - Aggregated relations are only compared, not used in arithmetic
*)
| ER_Aggregate :
    forall db
           (gcols : list ColName)
           (aggs  : list (ColName * aggop * ColName))
           q rows groups rows',
      evalRAR db q rows ->
      groups = group_by gcols rows ->
      rows' =
        map
          (fun grp =>
             {|
               r_schema := List.app gcols (map (fun '(newc, _, _) => newc) aggs);
               r_get :=
                 fun c =>
                   if in_dec string_dec c gcols then
                     group_key_value grp c
                   else
                     eval_agg grp c aggs
             |})
          groups ->
      evalRAR db (RAAggregate gcols aggs q) rows'.

